module

public import Froberg.RestoredCommonSelection
public import Froberg.ScalarVectorIndependenceOpen
public import Froberg.RestoredJointSelection

@[expose] public section

/-! All restored certificates hold on a nonempty principal open of the
full parameter space. This allows the generic child flag to be imposed
before restricting to the last positive-scalar fiber. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q r f : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

theorem restored_certificate_principal_open (hdp : 1≤d) (hd : d%2=0)
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
    ∃ E : MvPolynomial (Fin (finrank K (RestoredOuterSpace m d q f J counts O))) K,
      (∃ p : RestoredOuterSpace m d q f J counts O,eval ((Module.finBasis K _).equivFun p) E≠0) ∧
      ∀ p : RestoredOuterSpace m d q f J counts O,eval ((Module.finBasis K _).equivFun p) E≠0 →
        RestoredCertificate hdp hd hO hJ heven idx slot p := by
  letI : Module.Finite K (Space m d q J counts O) := finite_space hO
  let S := RestoredSpace m d q J counts O
  let V := RestoredOuterSpace m d q f J counts O
  let out := PreparedTarget.OuterSpace K (Fin h) m d f
  let π : V →ₗ[K] S := LinearMap.fst K S out
  have hπ : Function.Surjective π := fun p => ⟨(p,0),rfl⟩
  obtain ⟨P,hP,hred⟩ := even_prepared_restoration_principal_open hd hO hJ heven hpos idx slot hslot p₀ hp₀
  obtain ⟨R,hR,hRgood⟩ := principal_open_linear_pullback π hπ P ⟨(p₀,0),hP⟩ _ hred
  obtain ⟨D',hD',hDgood⟩ := principal_open_linear_pullback π hπ D hD _ hodd
  let U := Fin (finrank K (Forms K h d)) → Forms K h d
  let πU : V →ₗ[K] U := (LinearMap.snd K (Space m d q J counts O) U).comp π
  obtain ⟨P',hP',hPgood⟩ := finite_family_independence_open (K := K) (V := Forms K h d) (le_refl (finrank K (Forms K h d)))
  obtain ⟨B,hB,hBgood⟩ := principal_open_linear_pullback πU (fun v => ⟨((0,v),0),rfl⟩) P' hP' _ hPgood
  obtain ⟨I,hI,hIgood⟩ := hi
  obtain ⟨A,hA,hAgood⟩ := ho
  obtain ⟨T,hT,hTgood⟩ := hu
  let family := ![R,D',B,I,A,T]
  have hex : ∀ j : Fin 6,∃ p : V,eval ((Module.finBasis K _).equivFun p) (family j)≠0 := by
    intro j
    fin_cases j
    · exact hR
    · exact hD'
    · exact hB
    · exact hI
    · exact hA
    · exact hT
  obtain ⟨p,hp⟩ := finite_basis_principal_intersection family hex
  let E := R*D'*B*I*A*T
  refine ⟨E,⟨p,?_⟩,?_⟩
  · simpa [E,family,map_mul] using
      mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (hp 0) (hp 1)) (hp 2)) (hp 3)) (hp 4)) (hp 5)
  intro p hp
  have hall : eval ((Module.finBasis K _).equivFun p) R≠0 ∧
      eval ((Module.finBasis K _).equivFun p) D'≠0 ∧
      eval ((Module.finBasis K _).equivFun p) B≠0 ∧
      eval ((Module.finBasis K _).equivFun p) I≠0 ∧
      eval ((Module.finBasis K _).equivFun p) A≠0 ∧
      eval ((Module.finBasis K _).equivFun p) T≠0 := by
    simpa only [E,map_mul,mul_ne_zero_iff,and_assoc] using hp
  have hpure := hBgood p hall.2.2.1
  exact ⟨hpure,hpure.span_eq_top_of_card_eq_finrank' (Fintype.card_fin _),
    hIgood p hall.2.2.2.1,hAgood p hall.2.2.2.2.1,hTgood p hall.2.2.2.2.2,
    hDgood p hall.2.1,hRgood p hall.1⟩


/-- A fully restored certificate together with the generic lower-degree
child flag and the strict outer vector model, at the same parameter point. -/
def RestoredGenericCertificate (hdp : 1≤d) (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (G C : ℝ) (p : RestoredOuterSpace m d q f J counts O) : Prop :=
  RestoredCertificate hdp hd hO hJ heven idx slot p ∧
    VectorExpansionOpen.StrictModel (fun i => PreparedTarget.outerVectorEquiv.symm (p.2 i)) d G ∧
    ChildFlagCondition
      (VectorExpansionOpen.quotientMultiplication (fun i => PreparedTarget.outerVectorEquiv.symm (p.2 i)) d)
      (VectorExpansionOpen.outerScalarDeficit (fun i => PreparedTarget.outerVectorEquiv.symm (p.2 i))) C
      (coefficientCoordinates (fun i => p.1.1.1 (Sum.inl i)))

open Filter VectorExpansionOpen
open scoped Topology

/-- The exact-count child flag, all restored certificate conditions, and any
additional full open survive together on one nonempty positive-scalar fiber. -/
theorem exact_counts_restored_certified_fiber {d k h lo : ℕ}
    (hd : 3≤d) (hdeven : d%2=0) (hk : 0<k) (hh : h=k*centralHalfBinomial d) (hhpos : 0<h)
    (upper : Bool) (a f e : ℕ → ℕ) (ha : ∀ n,a n ≤ n)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    {δ : ℝ} (hδ : 0<δ)
    (hreserve : ∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n)) :
    ∃ G C : ℝ,0<G ∧ 0<C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Finset ℕ) (counts : ℕ → ℕ) (O : ℕ → Submodule K (Poly K h))
        (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
        (r : ℕ) (idx : Fin r ≃ Label (upperCount n d) J counts)
        (slot : Fin (finrank K (Forms K h d)) → Fin r),
      letI : Module.Finite K (Space n d (upperCount n d) J counts O) := finite_space hO
      ∀ P D : MvPolynomial (Fin (finrank K (RestoredOuterSpace n d (upperCount n d) (f n) J counts O))) K,
        (∃ p : RestoredOuterSpace n d (upperCount n d) (f n) J counts O,
          eval ((Module.finBasis K _).equivFun p) P≠0) →
        (∀ p : RestoredOuterSpace n d (upperCount n d) (f n) J counts O,
          eval ((Module.finBasis K _).equivFun p) P≠0 →
            RestoredCertificate (by omega) hdeven hO hJ heven idx slot p) →
        (∃ p : RestoredOuterSpace n d (upperCount n d) (f n) J counts O,
          eval ((Module.finBasis K _).equivFun p) D≠0) →
        ∃ (rest : RestoredScalarRest n d (upperCount n d) (f n) J counts O)
          (A : MvPolynomial (Fin (finrank K (PositiveScalars (K := K) n d J counts))) K),
          (∃ a₀ : PositiveScalars (K := K) n d J counts,eval ((Module.finBasis K _).equivFun a₀) A≠0) ∧
          ∀ a',eval ((Module.finBasis K _).equivFun a') A≠0 →
            let p := restoredScalarFiberCoordinates.symm (a',rest)
            eval ((Module.finBasis K _).equivFun p) D≠0 ∧
            RestoredGenericCertificate (by omega) hdeven hO hJ heven idx slot
              (G*(n : ℝ)^d) (C*(n : ℝ)^d) p := by
  obtain ⟨G,C,hG,hC,hjoint⟩ := exact_counts_restored_joint (K := K) hd hk hh hhpos upper a f e ha hc hδ hreserve
  refine ⟨G,C,hG,hC,?_⟩
  filter_upwards [hjoint] with n hn
  intro J counts O hO hJ heven r idx slot
  letI : Module.Finite K (Space n d (upperCount n d) J counts O) := finite_space hO
  intro P D hP hcert hD
  obtain ⟨v,hv⟩ := finite_basis_principal_intersection (V := RestoredOuterSpace n d (upperCount n d) (f n) J counts O) ![P,D] (by
    intro i
    fin_cases i
    · exact hP
    · exact hD)
  have hPD : ∃ p : RestoredOuterSpace n d (upperCount n d) (f n) J counts O,
      eval ((Module.finBasis K _).equivFun p) (P*D)≠0 :=
    ⟨v,by simpa [map_mul] using mul_ne_zero (hv 0) (hv 1)⟩
  obtain ⟨p,hp,hmodel,hchild⟩ := hn J counts O hO (P*D) hPD
  obtain ⟨A,hA,hgood⟩ := restored_joint_positive_scalar_fiber_at hO
    (G*(n : ℝ)^d) (C*(n : ℝ)^d) (P*D) p hp hmodel hchild
  refine ⟨(restoredScalarFiberCoordinates p).2,A,⟨(restoredScalarFiberCoordinates p).1,hA⟩,?_⟩
  intro a' ha'
  obtain ⟨hPD',hm,hc'⟩ := hgood a' ha'
  have hboth := mul_ne_zero_iff.mp (show
      eval ((Module.finBasis K _).equivFun (restoredScalarFiberCoordinates.symm
        (a',(restoredScalarFiberCoordinates p).2))) P *
      eval ((Module.finBasis K _).equivFun (restoredScalarFiberCoordinates.symm
        (a',(restoredScalarFiberCoordinates p).2))) D≠0 by simpa only [map_mul] using hPD')
  exact ⟨hboth.2,hcert _ hboth.1,hm,hc'⟩

end Froberg.PreparedParameters
