module

public import Froberg.CoveredEndpointReplacement
public import Froberg.BackgroundFlagMembership

@[expose] public section

/-! The covered replacement theorem applies to a scalar flag slot of
the actual even family, with every positive generator retained. -/
noncomputable section
set_option maxHeartbeats 300000
namespace Froberg
open Module MvPolynomial Quartic BilinearScalarFamily
variable {K : Type} [Field K] [Infinite K] {h m d q f u e : ℕ}

theorem update_append_left {V : Type*} (Q : Fin q → V) (E : Fin e → V) (i : Fin q) (x : V) :
    Function.update (Fin.append Q E) (Fin.castAdd e i) x=Fin.append (Function.update Q i x) E := by
  classical
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro k
    by_cases hk : k=i
    · subst k
      simp
    · rw [Function.update_of_ne (by exact fun he => hk (Fin.castAdd_injective q e he)),
        Fin.append_left,Fin.append_left,Function.update_of_ne hk]
  · intro k
    have hne : Fin.natAdd q k≠Fin.castAdd e i := by
      intro he
      have hv := congrArg Fin.val he
      have hi := i.isLt
      change q+k.val=i.val at hv
      omega
    rw [Function.update_of_ne hne,Fin.append_right,Fin.append_right]

private theorem predicate_reindex_cast {V : Type*} {a b : ℕ} (h : a=b)
    (P : (n : ℕ) → (Fin n → V) → Prop) (v : Fin b → V) :
    P a (v ∘ Fin.cast h) ↔ P b v := by
  subst b
  rfl

private theorem predicate_empty_append {V : Type*} {n : ℕ}
    (P : (n : ℕ) → (Fin n → V) → Prop) (v : Fin n → V) :
    P (0+n) (Fin.append (Fin.elim0 : Fin 0 → V) v) ↔ P n v := by
  rw [Fin.elim0_append]
  exact predicate_reindex_cast (Nat.zero_add n) P v

theorem exists_covered_background_slot_thin [IsAlgClosed K]
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (i : Fin q) (M : biformParitySpace K h m d 0) (C : ℝ)
    (D : Submodule K (Forms K (h+m) (2*d)))
    (hD : D≤(parityForm (coreParity h m) 1).ker)
    (hc : ∀ p,parityForm (coreParity h m) 0 p∈
      D ⊔ (endpointMultiplication (backgroundEnumeratedForms Q F G)).range)
    (hex : OddSplitExact Q (Fin.append F G))
    (hs : HasClosedKernelSlices (oddEndpointScalarAction Q F G)
      (BilinearCovectorStrata.thinSlices (backgroundOddTargetDimension Q F G) C))
    (hi : LinearIndependent K (backgroundEnumeratedForms Q F G))
    (hu : Function.Surjective (upperTargetMap (h := h) (m := m) (d := d)
      (backgroundEnumeratedForms Q F G)))
    (P : MvPolynomial (Fin 1) K) (hP : eval 0 P≠0) :
    ∃ c : K,c≠0 ∧ eval (fun _ => c) P≠0 ∧
      OddSplitExact (Function.update Q i (Q i+c • M)) (Fin.append F G) ∧
      HasClosedKernelSlices (oddEndpointScalarAction (Function.update Q i (Q i+c • M)) F G)
        (BilinearCovectorStrata.thinSlices
          (backgroundOddTargetDimension (Function.update Q i (Q i+c • M)) F G) C) ∧
      LinearIndependent K (backgroundEnumeratedForms (Function.update Q i (Q i+c • M)) F G) ∧
      Function.Surjective (upperTargetMap (h := h) (m := m) (d := d)
        (backgroundEnumeratedForms (Function.update Q i (Q i+c • M)) F G)) ∧
      ∀ p,parityForm (coreParity h m) 0 p∈D ⊔
        (endpointMultiplication (backgroundEnumeratedForms (Function.update Q i (Q i+c • M)) F G)).range := by
  let Good (r : ℕ) (S : Fin r → biformParitySpace K h m d 0) : Prop :=
    OddSplitExact S (Fin.append F G) ∧
    HasClosedKernelSlices (oddEndpointScalarAction S F G)
      (BilinearCovectorStrata.thinSlices (backgroundOddTargetDimension S F G) C) ∧
    LinearIndependent K (backgroundEnumeratedForms S F G) ∧
    Function.Surjective (upperTargetMap (h := h) (m := m) (d := d) (backgroundEnumeratedForms S F G)) ∧
    ∀ p,parityForm (coreParity h m) 0 p∈D ⊔
      (endpointMultiplication (backgroundEnumeratedForms S F G)).range
  have hg : Good (0+q) (Fin.append (Fin.elim0 : Fin 0 → biformParitySpace K h m d 0) Q) :=
    (predicate_empty_append Good Q).mpr ⟨hex,hs,hi,hu,hc⟩
  obtain ⟨c,hne,hpc,hx,hs',hi',hu',hc'⟩ := exists_covered_endpoint_slot_thin (q := 0)
    (Fin.elim0 : Fin 0 → biformParitySpace K h m d 0) F G Q i M C D hD
    hg.2.2.2.2 hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1 P hP
  have hout : Good q (Function.update Q i (Q i+c • M)) :=
    (predicate_empty_append Good _).mp ⟨hx,hs',hi',hu',hc'⟩
  exact ⟨c,hne,hpc,hout⟩

end Froberg
