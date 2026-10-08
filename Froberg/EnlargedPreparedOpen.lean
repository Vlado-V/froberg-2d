import Froberg.ActualPreparedComparison
import Froberg.CountedLeadingOpen
import Froberg.CountedPreparedOuterOpen
import Froberg.FiniteBasisPrincipalIntersection

/-! The independent geometric opens combine on one actual enlarged
prepared parameter space and supply all six comparison certificates. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial PreparedParameters FullPreparedParameters
variable {K : Type} [Field K] [CharZero K] [IsAlgClosed K]
variable {h m d q f u r : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (Poly K h)}

theorem hasEnlargedPreparedOpen_of_opens
    (hd : 0<d) (ho : d%2=1)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ PreparedParameters.Label q J counts) (U : Fin u → Forms K h d)
    (hbasic : HasBasicOpen (m := m) (q := q) (f := f) (counts := counts) hd hO hJ U)
    (hlead : HasLeadingPrivateOpen (n := m) (d := d) (q := q) (f := f) (u := u)
      (counts := counts) hO)
    (hred :
      letI : Module.Finite K (FixedPureZeroScalarSpace m d q f u J counts O) :=
        finite_fixedPureZeroScalarSpace hO
      ∃ D : MvPolynomial (Fin (finrank K (FixedPureZeroScalarSpace m d q f u J counts O))) K,
        (∃ p : FixedPureZeroScalarSpace m d q f u J counts O,
          eval ((Module.finBasis K _).equivFun p) D≠0) ∧
        ∀ p : FixedPureZeroScalarSpace m d q f u J counts O,
          eval ((Module.finBasis K _).equivFun p) D≠0 →
            PrivateSplitReduction hd ho hO hJ heven idx U p)
    (hsep : HasUniformPreparedOuterOpen (n := m) (q := q) (f := f) (u := u)
      (counts := counts) hd ho hO hJ heven) :
    HasEnlargedPreparedOpen (m := m) (f := f) hd ho hO hJ heven idx U := by
  classical
  letI : Module.Finite K (FixedPureZeroScalarSpace m d q f u J counts O) :=
    finite_fixedPureZeroScalarSpace hO
  obtain ⟨B,hB,hBg⟩ := hbasic
  obtain ⟨L,hL,hLg⟩ := hlead
  obtain ⟨R,hR,hRg⟩ := hred
  obtain ⟨S,hS,hSg⟩ := hsep
  let family := ![B,L,R,S]
  have hex : ∀ i : Fin 4,∃ p : FixedPureZeroScalarSpace m d q f u J counts O,
      eval ((Module.finBasis K _).equivFun p) (family i)≠0 := by
    intro i
    fin_cases i
    · exact hB
    · exact hL
    · exact hR
    · exact hS
  obtain ⟨p,hp⟩ := finite_basis_principal_intersection family hex
  refine ⟨B*L*R*S,⟨p,?_⟩,?_⟩
  · simpa [family,map_mul] using
      mul_ne_zero (mul_ne_zero (mul_ne_zero (hp 0) (hp 1)) (hp 2)) (hp 3)
  · intro p hp
    have hall :
        eval ((Module.finBasis K _).equivFun p) B≠0 ∧
        eval ((Module.finBasis K _).equivFun p) L≠0 ∧
        eval ((Module.finBasis K _).equivFun p) R≠0 ∧
        eval ((Module.finBasis K _).equivFun p) S≠0 := by
      simpa only [map_mul,mul_ne_zero_iff,and_assoc] using hp
    have hbasic := hBg p hall.1
    have hleading := hLg p hall.2.1
    exact ⟨hleading.1,hleading.2,hbasic.1,hbasic.2.1,
      hRg p hall.2.2.1,hSg U p hall.2.2.2⟩

end Froberg.PreparedTarget
