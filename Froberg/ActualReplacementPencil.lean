module

public import Froberg.OddEvenBottomDetection
public import Froberg.OddSplitComplex
public import Froberg.ClosedKernelEquivalence
public import Froberg.RangeQuotientSlices
public import Froberg.ReplacementParameter

@[expose] public section

/-! A literal even-generator replacement preserves odd exactness and all
closed scalar-contraction slices on one common nonzero parameter. The odd
coefficient quotient is fixed, while the target is the quotient by the
range of the actual relative even multiplication map. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module MvPolynomial Quartic BilinearScalarFamily
variable {K : Type} [Field K] [Infinite K] {h m d q f u e : ℕ}

theorem oddEvenScalar_compatible
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0)
    (p : Forms K m d)
    (v : biformParitySpace K h m d 1 ⧸ oddBackgroundCoefficientRelations F G) :
    oddEvenTargetExtensionEquiv Q F G E
      ((oddEvenRelativeMap Q F G E).range.mkQ (oddBackgroundScalarProduct Q F G p v))=
      oddBackgroundScalarProduct (Fin.append Q E) F G p v := by
  obtain ⟨a,rfl⟩ := (oddBackgroundCoefficientRelations F G).mkQ_surjective v
  exact oddEvenTargetExtensionEquiv_mk Q F G E (evenOddBiformProduct (scalarEvenBiform p) a)

theorem oddEvenScalar_slices_iff
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0) (s : ℕ → ℕ) :
    HasClosedKernelSlices
      (targetPostcompose (oddBackgroundScalarProduct Q F G)
        (oddEvenRelativeMap Q F G E).range.mkQ) s ↔
      HasClosedKernelSlices (oddBackgroundScalarProduct (Fin.append Q E) F G) s := by
  constructor
  · intro hs
    exact hs.equiv (LinearEquiv.refl K _) (LinearEquiv.refl K _)
      (oddEvenTargetExtensionEquiv Q F G E) _ _
      (oddEvenScalar_compatible Q F G E) s
  · intro hs
    apply hs.equiv (LinearEquiv.refl K _) (LinearEquiv.refl K _)
      (oddEvenTargetExtensionEquiv Q F G E).symm _ _ _ s
    intro p v
    apply (oddEvenTargetExtensionEquiv Q F G E).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (oddEvenScalar_compatible Q F G E p v).symm

theorem oddEvenRelativeMap_smul
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0) (c : K) :
    oddEvenRelativeMap Q F G (fun i => c • E i)=c • oddEvenRelativeMap Q F G E := by
  apply LinearMap.ext
  intro a
  simp only [oddEvenRelativeMap_apply,map_smul,LinearMap.smul_apply,Finset.smul_sum]

theorem odd_even_pencil_slices_open [IsAlgClosed K]
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (E D : Fin e → biformParitySpace K h m d 0) (s : ℕ → ℕ)
    (hs : HasClosedKernelSlices (oddBackgroundScalarProduct (Fin.append Q E) F G) s) :
    ∃ P : MvPolynomial (Fin 1) K,eval 0 P≠0 ∧ ∀ c : K,
      eval (fun _ => c) P≠0 → HasClosedKernelSlices
        (oddBackgroundScalarProduct (Fin.append Q (fun i => E i+c • D i)) F G) s := by
  obtain ⟨P,hP,hgood⟩ := quotient_pencil_slices_principal_open
    (oddBackgroundScalarProduct Q F G)
    (oddEvenRelativeMap Q F G E) (oddEvenRelativeMap Q F G D) s
    ((oddEvenScalar_slices_iff Q F G E s).mpr hs)
  refine ⟨P,hP,?_⟩
  intro c hc
  apply (oddEvenScalar_slices_iff Q F G _ s).mp
  rw [oddEvenRelativeMap_add,oddEvenRelativeMap_smul]
  exact hgood c hc

theorem odd_even_pencil_exact_open
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (E D : Fin e → biformParitySpace K h m d 0)
    (hex : OddSplitExact (Fin.append Q E) (Fin.append F G)) :
    ∃ P : MvPolynomial (Fin 1) K,eval 0 P≠0 ∧ ∀ c : K,
      eval (fun _ => c) P≠0 →
        OddSplitExact (Fin.append Q (fun i => E i+c • D i)) (Fin.append F G) := by
  let A : Fin (q+e) → (Fin 1 → K) → biformParitySpace K h m d 0 :=
    fun i p => Fin.append Q (fun j => E j+p 0 • D j) i
  have hA (i : Fin (q+e)) : IsPolynomialFamily (A i) := by
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [A,Fin.append_left] using isPolynomialFamily_const (ι := Fin 1) (Q j)
    · intro j
      simpa only [A,Fin.append_right,LinearMap.proj_apply] using (isPolynomialFamily_const (E j)).add
        ((isPolynomialFamily_linear (LinearMap.proj (0 : Fin 1))).smul
          (isPolynomialFamily_const (D j)))
  obtain ⟨P,hP,hgood⟩ := odd_split_exact_principal_open A
    (fun j (_ : Fin 1 → K) => Fin.append F G j) hA
    (fun j => isPolynomialFamily_const _) 0 (by simpa only [A,Pi.zero_apply,zero_smul,add_zero] using hex)
  exact ⟨P,hP,fun c hc => hgood (fun _ => c) hc⟩

theorem exists_actual_even_pencil_replacement [IsAlgClosed K]
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (E D : Fin e → biformParitySpace K h m d 0) (s : ℕ → ℕ)
    (hex : OddSplitExact (Fin.append Q E) (Fin.append F G))
    (hs : HasClosedKernelSlices (oddBackgroundScalarProduct (Fin.append Q E) F G) s)
    (P : MvPolynomial (Fin 1) K) (hP : eval 0 P≠0) :
    ∃ c : K,c≠0 ∧ eval (fun _ => c) P≠0 ∧
      OddSplitExact (Fin.append Q (fun i => E i+c • D i)) (Fin.append F G) ∧
      HasClosedKernelSlices
        (oddBackgroundScalarProduct (Fin.append Q (fun i => E i+c • D i)) F G) s := by
  obtain ⟨A,hA,ha⟩ := odd_even_pencil_exact_open Q F G E D hex
  obtain ⟨B,hB,hb⟩ := odd_even_pencil_slices_open Q F G E D s hs
  obtain ⟨c,hc,hgood⟩ := exists_nonzero_replacement_fin (P*(A*B))
    (by simpa only [map_mul] using mul_ne_zero hP (mul_ne_zero hA hB))
  have hg : eval (fun _ => c) P≠0 ∧ eval (fun _ => c) A≠0 ∧ eval (fun _ => c) B≠0 := by
    simpa only [map_mul,mul_ne_zero_iff] using hgood
  exact ⟨c,hc,hg.1,ha c hg.2.1,hb c hg.2.2⟩

theorem exists_actual_even_slot_replacement [IsAlgClosed K]
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0) (i : Fin e)
    (M : biformParitySpace K h m d 0) (s : ℕ → ℕ)
    (hex : OddSplitExact (Fin.append Q E) (Fin.append F G))
    (hs : HasClosedKernelSlices (oddBackgroundScalarProduct (Fin.append Q E) F G) s)
    (P : MvPolynomial (Fin 1) K) (hP : eval 0 P≠0) :
    ∃ c : K,c≠0 ∧ eval (fun _ => c) P≠0 ∧
      OddSplitExact (Fin.append Q (Function.update E i (E i+c • M))) (Fin.append F G) ∧
      HasClosedKernelSlices
        (oddBackgroundScalarProduct (Fin.append Q (Function.update E i (E i+c • M))) F G) s := by
  classical
  obtain ⟨c,hc,hP,hex,hs⟩ := exists_actual_even_pencil_replacement Q F G E
    (Pi.single i M) s hex hs P hP
  have he : (fun j => E j+c • (Pi.single i M : Fin e → biformParitySpace K h m d 0) j)=Function.update E i (E i+c • M) := by
    funext j
    by_cases hj : j=i
    · subst j
      simp
    · simp [hj]
  rw [he] at hex hs
  exact ⟨c,hc,hP,hex,hs⟩

end Froberg
