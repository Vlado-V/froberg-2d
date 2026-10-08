import Froberg.BiformRestoredRelations
import Froberg.PreparedRestorationOpen

/-! The restored common prepared family retains exactly the original
scalar relation space after the supported endpoint deletion. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {h m d q r : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (Poly K h)}

def restoredEndpointFamily (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts)
    (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredSpace m d q J counts O) : Fin r → Forms K (h+m) d :=
  biformRestorationForms (restoredFamilyLinear hd hO hJ heven idx slot p)

theorem restoredEndpointFamily_scalar (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts)
    (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (hslot : ∀ k,0<degree (idx (slot k)))
    (p : RestoredSpace m d q J counts O) (i : Fin r) (j : Fin q)
    (hidx : idx i=Sum.inl j) :
    restoredEndpointFamily hd hO hJ heven idx slot p i=
      renameForm (Fin.natAdd h) (p.1.1 (Sum.inl j)) := by
  have haw : ∀ k,slot k≠i := by
    intro k hk
    have hh := hslot k
    rw [hk,hidx] at hh
    change 0<0 at hh
    omega
  have heq : (restoredFamilyLinear hd hO hJ heven idx slot p i).val=
      rename Sum.inr (p.1.1 (Sum.inl j)).val := by
    change (evenGenerator hO hJ heven p.1 (idx i)+
      PolynomialRestoration.pureShift (pureEvenEmbed hd) slot p.2 i).val=_
    rw [pureShift_eq_zero_away _ _ _ _ haw,add_zero,hidx]
    change rename Sum.inr (p.1.1 (Sum.inl j)).val+0=_
    exact add_zero _
  apply Subtype.ext
  change rename (finSumFinEquiv : Fin h ⊕ Fin m → Fin (h+m))
      (restoredFamilyLinear hd hO hJ heven idx slot p i).val=_
  rw [heq,rename_rename]
  rfl

theorem prepared_restored_formal_relations (htwo : (2 : K)≠0) (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hpos : ∀ j∈J,0<j) (idx : Fin r ≃ Label q J counts)
    (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (hslot : ∀ k,0<degree (idx (slot k)))
    (p : RestoredSpace m d q J counts O)
    (hi : LinearIndependent K (restoredEndpointFamily hd hO hJ heven idx slot p))
    (D : Submodule K (Forms K (h+m) (2*d)))
    (hD : D≤(renameForm (K := K) (d := 2*d) (Fin.natAdd h : Fin m → Fin (h+m))).range)
    (hodd : ∀ a : (endpointMultiplication (restoredEndpointFamily hd hO hJ heven idx slot p)).ker,
      (∀ i,(a.val i).val.IsWeightedHomogeneous (coreParity h m) 1) →
      a.val∈oppositeKoszulSpace (restoredEndpointFamily hd hO hJ heven idx slot p) (fun _ => 0))
    (hreduce : ∀ c : Fin r → evenRestorationSpace (K := K) (outputWeight (σ := Fin h) (n := m)) d,
      PolynomialRestoration.row (evenRestorationSpace outputWeight d).subtype
        (positiveWeightProjection outputWeight d) (restoredFamilyLinear hd hO hJ heven idx slot p) c=0 →
      ∃ (M : Fin r → Fin r → K)
        (z : retainedScalarCoefficients (K := K) outputWeight d (fun i => degree (idx i))),
        c-coefficientBoundary (restoredFamilyLinear hd hO hJ heven idx slot p) M=z.val) :
    (D.mkQ.comp formalPolynomialMultiplication).ker ⊓
        formalMixed (Submodule.span K (Set.range (restoredEndpointFamily hd hO hJ heven idx slot p)))=
      (D.mkQ.comp formalPolynomialMultiplication).ker ⊓
        formalProducts ((Submodule.span K (Set.range (fun j : Fin q => p.1.1 (Sum.inl j)))).map
          (renameForm (Fin.natAdd h))) (renameForm (K := K) (d := d) (Fin.natAdd h : Fin m → Fin (h+m))).range := by
  apply biform_restored_supported_relations htwo
    (restoredFamilyLinear hd hO hJ heven idx slot p) hi D hD hodd
    (fun i => degree (idx i)) _ _ _ hreduce
  · rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨a,⟨j,rfl⟩,rfl⟩
    rw [←restoredEndpointFamily_scalar hd hO hJ heven idx slot hslot p
      (idx.symm (Sum.inl j)) j (idx.apply_symm_apply _)]
    exact Submodule.subset_span ⟨_,rfl⟩
  · intro i hi0
    cases hx : idx i with
    | inl j =>
      rw [show biformRestorationForms (restoredFamilyLinear hd hO hJ heven idx slot p) i=
        renameForm (Fin.natAdd h) (p.1.1 (Sum.inl j)) from
          restoredEndpointFamily_scalar hd hO hJ heven idx slot hslot p i j hx]
      exact ⟨_,Submodule.subset_span ⟨j,rfl⟩,rfl⟩
    | inr a =>
      rw [hx] at hi0
      have hp := hpos a.1.val a.1.property
      change a.1.val=0 at hi0
      omega

end Froberg.PreparedParameters
