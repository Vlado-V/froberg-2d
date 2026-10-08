import Froberg.PreparedRestoredRelations

/-! A common restored point retains any further open conditions, has a
pure basis, and gives the exact relation equality for every supported
scalar deletion. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {h m d q r : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (Poly K h)}

theorem exists_prepared_restored_relations_on_open (htwo : (2 : K)≠0) (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hpos : ∀ j∈J,0<j) (idx : Fin r ≃ Label q J counts)
    (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (hslot : ∀ k,0<degree (idx (slot k)))
    (p₀ : Space m d q J counts O) (hp₀ : EvenPositiveReduction p₀)
    (E : MvPolynomial (Fin (finrank K (RestoredSpace m d q J counts O))) K)
    (hE : ∃ p : RestoredSpace m d q J counts O,eval (restoredCoordinates hO p) E≠0)
    (hgood : ∀ p : RestoredSpace m d q J counts O,eval (restoredCoordinates hO p) E≠0 →
      LinearIndependent K (restoredEndpointFamily hd hO hJ heven idx slot p) ∧
      ∀ a : (endpointMultiplication (restoredEndpointFamily hd hO hJ heven idx slot p)).ker,
        (∀ i,(a.val i).val.IsWeightedHomogeneous (coreParity h m) 1) →
        a.val∈oppositeKoszulSpace (restoredEndpointFamily hd hO hJ heven idx slot p) (fun _ => 0)) :
    ∃ p : RestoredSpace m d q J counts O,
      eval (restoredCoordinates hO p) E≠0 ∧
      LinearIndependent K p.2 ∧ Submodule.span K (Set.range p.2)=⊤ ∧
      ∀ D : Submodule K (Forms K (h+m) (2*d)),
        D≤(renameForm (K := K) (d := 2*d) (Fin.natAdd h : Fin m → Fin (h+m))).range →
        (D.mkQ.comp formalPolynomialMultiplication).ker ⊓
            formalMixed (Submodule.span K (Set.range (restoredEndpointFamily hd hO hJ heven idx slot p)))=
          (D.mkQ.comp formalPolynomialMultiplication).ker ⊓
            formalProducts ((Submodule.span K (Set.range (fun j : Fin q => p.1.1 (Sum.inl j)))).map
              (renameForm (Fin.natAdd h)))
              (renameForm (K := K) (d := d) (Fin.natAdd h : Fin m → Fin (h+m))).range := by
  obtain ⟨p,hp,hbasis,hspan,hreduce⟩ := exists_even_restored_basis_on_open hd hO hJ heven hpos
    idx slot hslot p₀ hp₀ E hE
  refine ⟨p,hp,hbasis,hspan,?_⟩
  intro D hD
  exact prepared_restored_formal_relations htwo hd hO hJ heven hpos idx slot hslot p
    (hgood p hp).1 D hD (hgood p hp).2 hreduce

end Froberg.PreparedParameters
