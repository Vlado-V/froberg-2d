import Froberg.ScalarFlagReplacement
import Froberg.EndpointPreparedFlag
import Froberg.ReplacementSeparation

/-! A concrete canonical background gives the critical local comparison.
The nonzero replacement parameter, all properties of the replaced family,
and the endpoint coordinates are constructed internally. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace Froberg
open Module MvPolynomial Quartic BilinearScalarFamily
variable {K : Type} [Field K] [Infinite K] [IsAlgClosed K]
variable {h m d e f u : ℕ}

theorem exists_critical_comparison_of_concrete_background
    (htwo : (2 : K)≠0) (hm : 0 < m) (upper : Bool)
    (hcard : upperCount m d+e+f+u=adjacentCriticalCount upper (h+m) d)
    (D : Submodule K (Forms K (h+m) (2*d)))
    (hD : D≤(renameForm (K := K) (d := 2*d)
      (Fin.natAdd h : Fin m → Fin (h+m))).range)
    (Q : Fin (upperCount m d) → Forms K m d) (hQ : LinearIndependent K Q)
    (E : Fin e → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (M : biformParitySpace K h m d 0)
    (hpositive : LinearIndependent K (fun i : Option (Fin e ⊕ Fin u) =>
      (renameForm (K := K) (d := d) (Fin.natAdd h : Fin m → Fin (h+m))).range.mkQ
        (i.elim (evenPolynomialToForms M) (backgroundPositiveForms E G))))
    (hbackground : (D.mkQ.comp formalPolynomialMultiplication).ker ⊓
        formalMixed ((embeddedFlagSpace (renameForm (Fin.natAdd h)) Q ⊔
          Submodule.span K (Set.range (backgroundPositiveForms E G))) ⊔
            Submodule.span K {evenPolynomialToForms M})=
      (D.mkQ.comp formalPolynomialMultiplication).ker ⊓
        formalProducts (embeddedFlagSpace (renameForm (Fin.natAdd h)) Q)
          (renameForm (K := K) (d := d) (Fin.natAdd h : Fin m → Fin (h+m))).range)
    (hsep : formalSquare (Submodule.span K
        (Set.range (fun i => oddPolynomialToForms (F i)))) ⊓
      ((formalMixed ((embeddedFlagSpace (renameForm (Fin.natAdd h)) Q ⊔
          Submodule.span K (Set.range (backgroundPositiveForms E G))) ⊔
            Submodule.span K {evenPolynomialToForms M})).map
        (D.mkQ.comp formalPolynomialMultiplication)).comap
        (D.mkQ.comp (formalPolynomialMultiplication (K := K) (n := h+m) (d := d)))=⊥)
    (hi : LinearIndependent K (backgroundEnumeratedForms
      (Fin.append (fun i => scalarEvenBiform (h := h) (Q i)) E) F G))
    (hex : OddSplitExact
      (Fin.append (fun i => scalarEvenBiform (h := h) (Q i)) E) (Fin.append F G))
    (hu : Function.Surjective (upperTargetMap (h := h) (m := m) (d := d)
      (backgroundEnumeratedForms (Fin.append (fun i => scalarEvenBiform (h := h) (Q i)) E) F G)))
    (hcoverage : ∀ p,parityForm (coreParity h m) 0 p∈D ⊔
      (endpointMultiplication (backgroundEnumeratedForms
        (Fin.append (fun i => scalarEvenBiform (h := h) (Q i)) E) F G)).range)
    (C : ℝ) (hC : (f : ℝ)≤C)
    (hslices : HasClosedKernelSlices (oddEndpointScalarAction
      (Fin.append (fun i => scalarEvenBiform (h := h) (Q i)) E) F G)
      (BilinearCovectorStrata.thinSlices (backgroundOddTargetDimension
        (Fin.append (fun i => scalarEvenBiform (h := h) (Q i)) E) F G) C))
    (hgeneric : finrank K (EndpointHomology (scalarFlagPrefix Q))=
      genericHomology K m d (upperCount m d-1))
    (hinj : Set.InjOn (D.mkQ.comp (renameForm (Fin.natAdd h)))
      (endpointMultiplication (scalarFlagPrefix Q)).range)
    (hdeleted : finrank K D=genericCokernel K m d (upperCount m d)) :
    Nonempty (LocalComparisonData K (h+m) d
      (adjacentCriticalCount upper (h+m) d) (criticalDefect K m d)) := by
  classical
  let S : Fin (upperCount m d) → biformParitySpace K h m d 0 :=
    fun i => scalarEvenBiform (Q i)
  let i := lastScalarSlot (upperCount_pos hm d)
  have hDodd : D≤(parityForm (coreParity h m) 1).ker := by
    intro p hp
    exact supported_deletion_odd_zero D hD p ((Submodule.Quotient.mk_eq_zero D).mpr hp)
  let Good (A : Fin (upperCount m d+e) → biformParitySpace K h m d 0) : Prop :=
    OddSplitExact A (Fin.append F G) ∧
    HasClosedKernelSlices (oddEndpointScalarAction A F G)
      (BilinearCovectorStrata.thinSlices (backgroundOddTargetDimension A F G) C) ∧
    LinearIndependent K (backgroundEnumeratedForms A F G) ∧
    Function.Surjective (upperTargetMap (h := h) (m := m) (d := d)
      (backgroundEnumeratedForms A F G)) ∧
    ∀ p,parityForm (coreParity h m) 0 p∈D ⊔
      (endpointMultiplication (backgroundEnumeratedForms A F G)).range
  obtain ⟨c,hc,_,hgood⟩ :=
    exists_covered_background_slot_thin (Fin.append S E) F G (Fin.castAdd e i) M C
      D hDodd hcoverage hex hslices hi hu 1 (by simp)
  change Good (Function.update (Fin.append S E) (Fin.castAdd e i)
    (Fin.append S E (Fin.castAdd e i)+c • M)) at hgood
  rw [Fin.append_left,update_append_left] at hgood
  let S' := Fin.append (Function.update S i (S i+c • M)) E
  have hgood' : Good S' := hgood
  obtain ⟨hex',hs',hi',hu',hcoverage'⟩ := hgood'
  have hF : LinearIndependent K (fun j => oddPolynomialToForms (F j)) := by
    have hAll := hi.comp (Fintype.equivFin (BackgroundLabel (upperCount m d+e) f u))
      (Fintype.equivFin _).injective
    rw [backgroundEnumeratedForms_reindex] at hAll
    simpa only [Function.comp_def,Sum.elim_inr,Sum.elim_inl] using
      hAll.comp (fun j : Fin f => (Sum.inr (Sum.inl j) : BackgroundLabel (upperCount m d+e) f u))
        (fun _ _ hEq => Sum.inl.inj (Sum.inr.inj hEq))
  have hr : Fintype.card (BackgroundLabel (upperCount m d+e) f u)=
      adjacentCriticalCount upper (h+m) d := by
    simpa only [BackgroundLabel,Fintype.card_sum,Fintype.card_fin,Nat.add_assoc] using hcard
  have hphi : ∀ p : Forms K m d,(scalarEndpointEmbedding (h := h) p).val.IsWeightedHomogeneous
      (coreParity h m) 0 := by
    intro p
    simpa only [coreParity_eq_blockParity] using scalarEndpointEmbedding_parity (h := h) p
  have hs'actual : HasClosedKernelSlices
      (oddQuotientProduct (coreParity h m) (backgroundEnumeratedForms S' F G)
        scalarEndpointEmbedding hphi)
      (BilinearCovectorStrata.thinSlices
        (finrank K (oddTargetSpace (coreParity h m) (backgroundEnumeratedForms S' F G))) C) := by
    revert hphi
    rw [coreParity_eq_blockParity]
    intro hphi
    simpa only [oddEndpointScalarAction_eq,backgroundOddTargetDimension]
      using hs'
  apply exists_critical_comparison_of_endpoint_flag htwo hm upper hr D hD Q hQ
    (backgroundPositiveForms E G) (evenPolynomialToForms M) hpositive hbackground c hc
    (backgroundEnumeratedForms S' F G) hi'
    (indexedSplitParity (backgroundSplitIndex (q := upperCount m d+e) (f := f) (u := u)))
    (backgroundEnumeratedForms_split_parity S' F G)
    (odd_split_background_endpoint S' F G hex')
    (fun j => oddPolynomialToForms (F j)) hF
    (background_replaced_flag_span Q (upperCount_pos hm d) E F G M c)
    (background_replaced_even_mem Q (upperCount_pos hm d) E F G M c)
    (flag_replacement_separation (renameForm (Fin.natAdd h)) Q (upperCount_pos hm d)
      (backgroundPositiveForms E G) (evenPolynomialToForms M) c
      (D.mkQ.comp formalPolynomialMultiplication)
      (Submodule.span K (Set.range (fun j => oddPolynomialToForms (F j)))) hsep)
    hcoverage' scalarEndpointEmbedding hphi C hC hs'actual hgeneric hinj hdeleted

end Froberg
