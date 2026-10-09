module

public import Froberg.PreparedCountedOddCycles
public import Froberg.PreparedIndependenceOpen
public import Froberg.FiniteBasisPrincipalIntersection

@[expose] public section

/-! Independence and odd-cycle exactness hold on a single explicit
principal open inside any supplied nonempty prepared-parameter open. -/
noncomputable section
set_option maxHeartbeats 100000
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

theorem exists_prepared_independent_odd_certificate_open (hd : 0 < d)
    (hO : ∀ j ∈ J, O j ≤ Forms K h j) (hJ : ∀ j ∈ J, j ≤ d)
    (hi : HasIndependentOpen (m := m) (q := q) (f := f) (u := u)
      (counts := counts) hd hO hJ)
    (ho : HasOddCyclesOpen (m := m) (d := d) (q := q) (f := f) (u := u)
      (counts := counts) hO) :
    letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) :=
      FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
    ∀ D : MvPolynomial (Fin (finrank K
      (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O))) K,
      (∃ p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O,
        eval ((Module.finBasis K _).equivFun p) D ≠ 0) →
      ∃ D' : MvPolynomial (Fin (finrank K
        (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O))) K,
        (∃ p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O,
          eval ((Module.finBasis K _).equivFun p) D' ≠ 0) ∧
        ∀ p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O,
          eval ((Module.finBasis K _).equivFun p) D' ≠ 0 →
          eval ((Module.finBasis K _).equivFun p) D ≠ 0 ∧
          ∀ U : Fin u → Forms K h d,
            LinearIndependent K (zeroScalarEndpointFamily hd hO hJ U p.1 p.2) ∧
            OddCyclesExact U p.1 p.2 := by
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  intro D hD
  obtain ⟨I,hI,higood⟩ := hi
  obtain ⟨C,hC,hcgood⟩ := ho
  let family := ![I,C,D]
  have hex : ∀ j : Fin 3,
      ∃ p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O,
        eval ((Module.finBasis K _).equivFun p) (family j) ≠ 0 := by
    intro j
    fin_cases j
    · exact hI
    · exact hC
    · exact hD
  obtain ⟨p,hp⟩ := finite_basis_principal_intersection family hex
  refine ⟨I*C*D,⟨p,?_⟩,?_⟩
  · simpa [family,map_mul] using mul_ne_zero (mul_ne_zero (hp 0) (hp 1)) (hp 2)
  · intro x hx
    have hx' : (eval ((Module.finBasis K _).equivFun x) I ≠ 0 ∧
        eval ((Module.finBasis K _).equivFun x) C ≠ 0) ∧
        eval ((Module.finBasis K _).equivFun x) D ≠ 0 := by
      simpa only [map_mul,mul_ne_zero_iff] using hx
    exact ⟨hx'.2,fun U => ⟨higood x hx'.1.1 U,hcgood x hx'.1.2 U⟩⟩

end Froberg.PreparedTarget
