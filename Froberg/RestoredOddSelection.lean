module

public import Froberg.PreparedCountedRestoredOdd

@[expose] public section

/-! Odd injection is imposed on the same restored parameters as the pure
basis and the even-row reduction, together with any further principal open. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Quartic
variable {K : Type} [Field K] [Infinite K]
variable {h m d q r : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (Poly K h)}

theorem exists_even_restored_odd_basis_on_open (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hpos : ∀ j∈J,0<j) (idx : Fin r ≃ Label q J counts)
    (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (hslot : ∀ k,0<degree (idx (slot k)))
    (p₀ : Space m d q J counts O) (hp₀ : EvenPositiveReduction p₀)
    (D : MvPolynomial (Fin (finrank K (RestoredSpace m d q J counts O))) K)
    (hD : ∃ p : RestoredSpace m d q J counts O,eval (restoredCoordinates hO p) D≠0)
    (hodd : ∀ p : RestoredSpace m d q J counts O,eval (restoredCoordinates hO p) D≠0 →
      Function.Injective (restoredOddRowLinear (restoredFamilyLinear hd hO hJ heven idx slot p)))
    (E : MvPolynomial (Fin (finrank K (RestoredSpace m d q J counts O))) K)
    (hE : ∃ p : RestoredSpace m d q J counts O,eval (restoredCoordinates hO p) E≠0) :
    ∃ p : RestoredSpace m d q J counts O,
      eval (restoredCoordinates hO p) E≠0 ∧
      LinearIndependent K p.2 ∧ Submodule.span K (Set.range p.2)=⊤ ∧
      Function.Injective (restoredOddRowLinear (restoredFamilyLinear hd hO hJ heven idx slot p)) ∧
      ∀ c : Fin r → evenRestorationSpace (K := K) (outputWeight (σ := Fin h) (n := m)) d,
        PolynomialRestoration.row (evenRestorationSpace outputWeight d).subtype
          (positiveWeightProjection outputWeight d) (restoredFamilyLinear hd hO hJ heven idx slot p) c=0 →
        ∃ (M : Fin r → Fin r → K)
          (z : retainedScalarCoefficients (K := K) outputWeight d (fun i => degree (idx i))),
          c-coefficientBoundary (restoredFamilyLinear hd hO hJ heven idx slot p) M=z.val := by
  let coord : RestoredSpace m d q J counts O ≃ₗ[K]
      (Fin (finrank K (RestoredSpace m d q J counts O)) → K) := restoredCoordinates hO
  have hDE : ∃ p : RestoredSpace m d q J counts O,eval (coord p) (D*E)≠0 := by
    obtain ⟨pD,hpD⟩ := hD
    obtain ⟨pE,hpE⟩ := hE
    obtain ⟨a,haD,haE⟩ := principal_opens_intersect ⟨coord pD,hpD⟩ ⟨coord pE,hpE⟩
    refine ⟨coord.symm a,?_⟩
    simpa only [LinearEquiv.apply_symm_apply,map_mul] using mul_ne_zero haD haE
  obtain ⟨p,hp,hbasis,hspan,hreduce⟩ := exists_even_restored_basis_on_open hd hO hJ heven
    hpos idx slot hslot p₀ hp₀ (D*E) hDE
  have hpDE : eval (coord p) D≠0 ∧ eval (coord p) E≠0 := by
    simpa only [map_mul,mul_ne_zero_iff] using hp
  exact ⟨p,hpDE.2,hbasis,hspan,hodd p hpDE.1,hreduce⟩

end Froberg.PreparedParameters
