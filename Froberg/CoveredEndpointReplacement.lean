import Froberg.ActualEndpointReplacement
import Froberg.OddExactEnumeration
import Froberg.EvenCoverageOpen

/-! One replacement preserves the full even-target coverage as well as
the odd C.4 slices. Thus the fixed-deletion projected target remains the
actual odd target after the scalar flag has changed. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module MvPolynomial Quartic BilinearScalarFamily
variable {K : Type} [Field K] [Infinite K] {h m d q f u e : ℕ}

theorem background_appended_slot_polynomial
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0) (i : Fin e)
    (M : biformParitySpace K h m d 0) :
    IsPolynomialFamily (fun p : Fin 1 → K =>
      backgroundEnumeratedForms (Fin.append Q (Function.update E i (E i+p 0 • M))) F G) := by
  classical
  let B : Fin (q+e) → biformParitySpace K h m d 0 := Fin.append 0 (Pi.single i M)
  have he (p : Fin 1 → K) : (fun j => Fin.append Q E j+p 0 • B j)=
      Fin.append Q (Function.update E i (E i+p 0 • M)) := by
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro j
      simp only [B,Fin.append_left,Pi.zero_apply,smul_zero,add_zero]
    · intro j
      by_cases hj : j=i
      · subst j
        simp [B]
      · simp [B,hj]
  have hpoly := background_pencil_polynomial (Fin.append Q E) B F G
  have hfun : (fun p : Fin 1 → K => backgroundEnumeratedForms
      (fun j => Fin.append Q E j+p 0 • B j) F G)=
      fun p => backgroundEnumeratedForms (Fin.append Q (Function.update E i (E i+p 0 • M))) F G := by
    funext p
    rw [he]
  rwa [hfun] at hpoly

attribute [local irreducible] backgroundEnumeratedForms oddEndpointScalarAction

theorem appended_slot_even_coverage_open
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0) (i : Fin e)
    (M : biformParitySpace K h m d 0)
    (D : Submodule K (Forms K (h+m) (2*d)))
    (hD : D≤(parityForm (coreParity h m) 1).ker)
    (hc : ∀ p,parityForm (coreParity h m) 0 p∈
      D ⊔ (endpointMultiplication (backgroundEnumeratedForms (Fin.append Q E) F G)).range) :
    ∃ P : MvPolynomial (Fin 1) K,eval 0 P≠0 ∧ ∀ c : K,eval (fun _ => c) P≠0 →
      ∀ p,parityForm (coreParity h m) 0 p∈D ⊔
        (endpointMultiplication (backgroundEnumeratedForms
          (Fin.append Q (Function.update E i (E i+c • M))) F G)).range := by
  let A := fun p : Fin 1 → K =>
    backgroundEnumeratedForms (Fin.append Q (Function.update E i (E i+p 0 • M))) F G
  obtain ⟨P,hP,hgood⟩ := even_coverage_principal_open D (coreParity h m)
    (indexedSplitParity (backgroundSplitIndex (q := q+e) (f := f) (u := u))) A
    (background_appended_slot_polynomial Q F G E i M) hD
    (fun p => backgroundEnumeratedForms_split_parity _ F G) 0
    (by simpa only [A,Pi.zero_apply,zero_smul,add_zero,Function.update_eq_self] using hc)
  exact ⟨P,hP,fun c hc => hgood (fun _ => c) hc⟩

theorem exists_covered_endpoint_slot_thin [IsAlgClosed K]
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0) (i : Fin e)
    (M : biformParitySpace K h m d 0) (C : ℝ)
    (D : Submodule K (Forms K (h+m) (2*d)))
    (hD : D≤(parityForm (coreParity h m) 1).ker)
    (hc : ∀ p,parityForm (coreParity h m) 0 p∈
      D ⊔ (endpointMultiplication (backgroundEnumeratedForms (Fin.append Q E) F G)).range)
    (hex : OddSplitExact (Fin.append Q E) (Fin.append F G))
    (hs : HasClosedKernelSlices (oddEndpointScalarAction (Fin.append Q E) F G)
      (BilinearCovectorStrata.thinSlices (backgroundOddTargetDimension (Fin.append Q E) F G) C))
    (hi : LinearIndependent K (backgroundEnumeratedForms (Fin.append Q E) F G))
    (hu : Function.Surjective (upperTargetMap (h := h) (m := m) (d := d)
      (backgroundEnumeratedForms (Fin.append Q E) F G)))
    (P : MvPolynomial (Fin 1) K) (hP : eval 0 P≠0) :
    ∃ c : K,c≠0 ∧ eval (fun _ => c) P≠0 ∧
      OddSplitExact (Fin.append Q (Function.update E i (E i+c • M))) (Fin.append F G) ∧
      HasClosedKernelSlices
        (oddEndpointScalarAction (Fin.append Q (Function.update E i (E i+c • M))) F G)
        (BilinearCovectorStrata.thinSlices
          (backgroundOddTargetDimension (Fin.append Q (Function.update E i (E i+c • M))) F G) C) ∧
      LinearIndependent K
        (backgroundEnumeratedForms (Fin.append Q (Function.update E i (E i+c • M))) F G) ∧
      Function.Surjective (upperTargetMap (h := h) (m := m) (d := d)
        (backgroundEnumeratedForms (Fin.append Q (Function.update E i (E i+c • M))) F G)) ∧
      ∀ p,parityForm (coreParity h m) 0 p∈D ⊔
        (endpointMultiplication (backgroundEnumeratedForms
          (Fin.append Q (Function.update E i (E i+c • M))) F G)).range := by
  obtain ⟨R,hR,hr⟩ := appended_slot_even_coverage_open Q F G E i M D hD hc
  obtain ⟨c,hne,hgood,he,hs',hi',hu'⟩ := exists_actual_endpoint_slot_thin Q F G E i M C
    hex hs hi hu (P*R) (by simpa only [map_mul] using mul_ne_zero hP hR)
  have hg : eval (fun _ => c) P≠0 ∧ eval (fun _ => c) R≠0 := by
    simpa only [map_mul,mul_ne_zero_iff] using hgood
  exact ⟨c,hne,hg.1,he,hs',hi',hu',hr c hg.2⟩

end Froberg
