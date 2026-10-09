module

public import Froberg.ActualReplacementRanks
public import Froberg.OddEndpointScalarSlices
public import Froberg.OddRelativeDimensions
public import Froberg.OddSplitRelativeInjection

@[expose] public section

/-! The common nonzero replacement is expressed on the literal endpoint
odd scalar action, with generator independence and B.7 surjectivity. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial Quartic BilinearScalarFamily
variable {K : Type} [Field K] [Infinite K] {h m d q f u e : ℕ}

theorem oddBackgroundScalar_endpoint_slices_iff
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1) (s : ℕ → ℕ) :
    HasClosedKernelSlices (oddBackgroundScalarProduct Q F G) s ↔
      HasClosedKernelSlices (oddEndpointScalarAction Q F G) s := by
  have hcompat (p : Forms K m d)
      (v : biformParitySpace K h m d 1 ⧸ oddBackgroundCoefficientRelations F G) :
      oddBackgroundEndpointEquiv Q F G (oddBackgroundScalarProduct Q F G p v)=
        oddEndpointScalarAction Q F G p (oddBackgroundSourceEquiv Q F G v) :=
    oddBackgroundQuotientProduct_compatible Q F G (scalarEvenBiform p) v
  constructor
  · intro hs
    exact hs.equiv (LinearEquiv.refl K _) (oddBackgroundSourceEquiv Q F G)
      (oddBackgroundEndpointEquiv Q F G) _ _ hcompat s
  · intro hs
    apply hs.equiv (LinearEquiv.refl K _) (oddBackgroundSourceEquiv Q F G).symm
      (oddBackgroundEndpointEquiv Q F G).symm _ _ _ s
    intro p v
    apply (oddBackgroundEndpointEquiv Q F G).injective
    rw [LinearEquiv.apply_symm_apply]
    have hh := hcompat p ((oddBackgroundSourceEquiv Q F G).symm v)
    rw [LinearEquiv.apply_symm_apply] at hh
    exact hh.symm

theorem exists_actual_endpoint_pencil [IsAlgClosed K]
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (E D : Fin e → biformParitySpace K h m d 0) (s : ℕ → ℕ)
    (hex : OddSplitExact (Fin.append Q E) (Fin.append F G))
    (hs : HasClosedKernelSlices (oddEndpointScalarAction (Fin.append Q E) F G) s)
    (hi : LinearIndependent K (backgroundEnumeratedForms (Fin.append Q E) F G))
    (hu : Function.Surjective (upperTargetMap (h := h) (m := m) (d := d) (backgroundEnumeratedForms (Fin.append Q E) F G)))
    (P : MvPolynomial (Fin 1) K) (hP : eval 0 P≠0) :
    ∃ c : K,c≠0 ∧ eval (fun _ => c) P≠0 ∧
      OddSplitExact (Fin.append Q (fun i => E i+c • D i)) (Fin.append F G) ∧
      HasClosedKernelSlices
        (oddEndpointScalarAction (Fin.append Q (fun i => E i+c • D i)) F G) s ∧
      LinearIndependent K (backgroundEnumeratedForms (Fin.append Q (fun i => E i+c • D i)) F G) ∧
      Function.Surjective (upperTargetMap (h := h) (m := m) (d := d)
        (backgroundEnumeratedForms (Fin.append Q (fun i => E i+c • D i)) F G)) := by
  obtain ⟨c,hc,hP,hex,hs,hi,hu⟩ := exists_actual_even_pencil_all_properties Q F G E D s hex
    ((oddBackgroundScalar_endpoint_slices_iff (Fin.append Q E) F G s).mpr hs) hi hu P hP
  exact ⟨c,hc,hP,hex,(oddBackgroundScalar_endpoint_slices_iff _ F G s).mp hs,hi,hu⟩

theorem exists_actual_endpoint_slot_replacement [IsAlgClosed K]
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0) (i : Fin e)
    (M : biformParitySpace K h m d 0) (s : ℕ → ℕ)
    (hex : OddSplitExact (Fin.append Q E) (Fin.append F G))
    (hs : HasClosedKernelSlices (oddEndpointScalarAction (Fin.append Q E) F G) s)
    (hi : LinearIndependent K (backgroundEnumeratedForms (Fin.append Q E) F G))
    (hu : Function.Surjective (upperTargetMap (h := h) (m := m) (d := d) (backgroundEnumeratedForms (Fin.append Q E) F G)))
    (P : MvPolynomial (Fin 1) K) (hP : eval 0 P≠0) :
    ∃ c : K,c≠0 ∧ eval (fun _ => c) P≠0 ∧
      OddSplitExact (Fin.append Q (Function.update E i (E i+c • M))) (Fin.append F G) ∧
      HasClosedKernelSlices
        (oddEndpointScalarAction (Fin.append Q (Function.update E i (E i+c • M))) F G) s ∧
      LinearIndependent K
        (backgroundEnumeratedForms (Fin.append Q (Function.update E i (E i+c • M))) F G) ∧
      Function.Surjective (upperTargetMap (h := h) (m := m) (d := d)
        (backgroundEnumeratedForms (Fin.append Q (Function.update E i (E i+c • M))) F G)) := by
  classical
  obtain ⟨c,hc,hP,hex,hs,hi,hu⟩ := exists_actual_endpoint_pencil Q F G E (Pi.single i M) s
    hex hs hi hu P hP
  have he : (fun j => E j+c • (Pi.single i M : Fin e → biformParitySpace K h m d 0) j)=
      Function.update E i (E i+c • M) := by
    funext j
    by_cases hj : j=i
    · subst j
      simp
    · simp [hj]
  rw [he] at hex hs hi hu
  exact ⟨c,hc,hP,hex,hs,hi,hu⟩


def backgroundOddTargetDimension
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1) : ℕ :=
  finrank K (oddTargetSpace
    ((fun i => (blockWeight h m i : ZMod 2)) ∘ finSumFinEquiv.symm)
    (backgroundEnumeratedForms Q F G))

theorem odd_endpoint_dimension_eq_of_split_exact
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (E E' : Fin e → biformParitySpace K h m d 0)
    (hE : OddSplitExact (Fin.append Q E) (Fin.append F G))
    (hE' : OddSplitExact (Fin.append Q E') (Fin.append F G)) :
    backgroundOddTargetDimension (Fin.append Q E') F G=
      backgroundOddTargetDimension (Fin.append Q E) F G := by
  have h0 := odd_even_relative_dimension Q F G E (odd_split_relative_injective Q F G E hE)
  have h1 := odd_even_relative_dimension Q F G E' (odd_split_relative_injective Q F G E' hE')
  have e0 := (oddBackgroundEndpointEquiv (Fin.append Q E) F G).finrank_eq
  have e1 := (oddBackgroundEndpointEquiv (Fin.append Q E') F G).finrank_eq
  dsimp only [backgroundOddTargetDimension]
  omega

theorem exists_actual_endpoint_slot_thin [IsAlgClosed K]
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0) (i : Fin e)
    (M : biformParitySpace K h m d 0) (C : ℝ)
    (hex : OddSplitExact (Fin.append Q E) (Fin.append F G))
    (hs : HasClosedKernelSlices (oddEndpointScalarAction (Fin.append Q E) F G)
      (BilinearCovectorStrata.thinSlices (backgroundOddTargetDimension (Fin.append Q E) F G) C))
    (hi : LinearIndependent K (backgroundEnumeratedForms (Fin.append Q E) F G))
    (hu : Function.Surjective (upperTargetMap (h := h) (m := m) (d := d) (backgroundEnumeratedForms (Fin.append Q E) F G)))
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
        (backgroundEnumeratedForms (Fin.append Q (Function.update E i (E i+c • M))) F G)) := by
  obtain ⟨c,hc,hP,hex',hs',hi',hu'⟩ := exists_actual_endpoint_slot_replacement Q F G E i M _
    hex hs hi hu P hP
  refine ⟨c,hc,hP,hex',?_,hi',hu'⟩
  rw [odd_endpoint_dimension_eq_of_split_exact Q F G E _ hex hex']
  exact hs'

end Froberg
