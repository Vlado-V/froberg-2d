import Froberg.ActualReplacementPencil
import Froberg.UpperTargetOpen
import Quartic.PolynomialRankOpen

/-! Independence and the full B.7 target surjection are preserved for the
same literal replacement family and the same nonzero parameter as C.4. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial Quartic BilinearScalarFamily
variable {K : Type} [Field K] [Infinite K] {h m d q f u e : ℕ}

theorem backgroundEnumeratedForms_pencil
    (Q D : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1) (c : K) :
    backgroundEnumeratedForms (fun i => Q i+c • D i) F G=
      backgroundEnumeratedForms Q F G+c • backgroundEnumeratedForms D 0 0 := by
  funext i
  apply Subtype.ext
  change rename finSumFinEquiv
      (backgroundParityFamily (fun j => Q j+c • D j) F G ((Fintype.equivFin _).symm i)).val=
    rename finSumFinEquiv (backgroundParityFamily Q F G ((Fintype.equivFin _).symm i)).val+
      c • rename finSumFinEquiv (backgroundParityFamily D 0 0 ((Fintype.equivFin _).symm i)).val
  rcases (Fintype.equivFin (BackgroundLabel q f u)).symm i with j | (j | j)
  · simp only [backgroundParityFamily,Submodule.coe_add,Submodule.coe_smul,map_add,map_smul]
  · simp only [backgroundParityFamily,Pi.zero_apply,Submodule.coe_zero,map_zero,smul_zero,add_zero]
  · simp only [backgroundParityFamily,Pi.zero_apply,Submodule.coe_zero,map_zero,smul_zero,add_zero]

theorem background_pencil_polynomial
    (Q D : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1) :
    IsPolynomialFamily (fun p : Fin 1 → K =>
      backgroundEnumeratedForms (fun i => Q i+p 0 • D i) F G) := by
  have he : (fun p : Fin 1 → K => backgroundEnumeratedForms (fun i => Q i+p 0 • D i) F G)=
      fun p => backgroundEnumeratedForms Q F G+p 0 • backgroundEnumeratedForms D 0 0 := by
    funext p
    exact backgroundEnumeratedForms_pencil Q D F G (p 0)
  rw [he]
  simpa only [LinearMap.proj_apply] using
    (isPolynomialFamily_const (backgroundEnumeratedForms Q F G)).add
      ((isPolynomialFamily_linear (LinearMap.proj (0 : Fin 1))).smul
        (isPolynomialFamily_const (backgroundEnumeratedForms D 0 0)))

attribute [local irreducible] backgroundEnumeratedForms upperTargetMap

theorem polynomial_endpoint_rank_open {r : ℕ}
    (A : (Fin 1 → K) → Fin r → Forms K (h+m) d) (hA : IsPolynomialFamily A)
    (hi : LinearIndependent K (A 0))
    (hu : Function.Surjective (upperTargetMap (h := h) (m := m) (d := d) (A 0))) :
    ∃ P : MvPolynomial (Fin 1) K,eval 0 P≠0 ∧ ∀ c : K,eval (fun _ => c) P≠0 →
      LinearIndependent K (A (fun _ => c)) ∧
      Function.Surjective (upperTargetMap (h := h) (m := m) (d := d) (A (fun _ => c))) := by
  have hAi (i : Fin r) : IsPolynomialFamily (fun p => A p i) := by
    intro ell
    exact hA (ell.comp (LinearMap.proj i))
  obtain ⟨P,hP,hp⟩ := independent_polynomial_principal_open (fun i p => A p i) hAi 0 hi
  obtain ⟨S,hS,hs⟩ := upperTarget_principal_open (h := h) (m := m) (d := d) A hA 0 hu
  refine ⟨P*S,by simpa only [map_mul] using mul_ne_zero hP hS,?_⟩
  intro c hc
  have hc' : eval (fun _ => c) P≠0 ∧ eval (fun _ => c) S≠0 := by
    simpa only [map_mul,mul_ne_zero_iff] using hc
  exact ⟨hp _ hc'.1,hs _ hc'.2⟩

theorem background_pencil_rank_open
    (Q D : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (hi : LinearIndependent K (backgroundEnumeratedForms Q F G))
    (hu : Function.Surjective (upperTargetMap (h := h) (m := m) (d := d) (backgroundEnumeratedForms Q F G))) :
    ∃ P : MvPolynomial (Fin 1) K,eval 0 P≠0 ∧ ∀ c : K,eval (fun _ => c) P≠0 →
      LinearIndependent K (backgroundEnumeratedForms (fun i => Q i+c • D i) F G) ∧
      Function.Surjective (upperTargetMap (h := h) (m := m) (d := d) (backgroundEnumeratedForms (fun i => Q i+c • D i) F G)) := by
  let A : (Fin 1 → K) → Fin (Fintype.card (BackgroundLabel q f u)) → Forms K (h+m) d :=
    fun p => backgroundEnumeratedForms (fun i => Q i+p 0 • D i) F G
  have hzero : A 0=backgroundEnumeratedForms Q F G := by
    change backgroundEnumeratedForms (fun i => Q i+(0 : K) • D i) F G=_
    simp only [zero_smul,add_zero]
  apply polynomial_endpoint_rank_open (h := h) (m := m) (d := d) A
    (background_pencil_polynomial Q D F G)
  · rw [hzero]
    exact hi
  · rw [hzero]
    exact hu

theorem exists_actual_even_pencil_all_properties [IsAlgClosed K]
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (E D : Fin e → biformParitySpace K h m d 0) (s : ℕ → ℕ)
    (hex : OddSplitExact (Fin.append Q E) (Fin.append F G))
    (hs : HasClosedKernelSlices (oddBackgroundScalarProduct (Fin.append Q E) F G) s)
    (hi : LinearIndependent K (backgroundEnumeratedForms (Fin.append Q E) F G))
    (hu : Function.Surjective (upperTargetMap (h := h) (m := m) (d := d) (backgroundEnumeratedForms (Fin.append Q E) F G)))
    (P : MvPolynomial (Fin 1) K) (hP : eval 0 P≠0) :
    ∃ c : K,c≠0 ∧ eval (fun _ => c) P≠0 ∧
      OddSplitExact (Fin.append Q (fun i => E i+c • D i)) (Fin.append F G) ∧
      HasClosedKernelSlices
        (oddBackgroundScalarProduct (Fin.append Q (fun i => E i+c • D i)) F G) s ∧
      LinearIndependent K (backgroundEnumeratedForms (Fin.append Q (fun i => E i+c • D i)) F G) ∧
      Function.Surjective (upperTargetMap (h := h) (m := m) (d := d)
        (backgroundEnumeratedForms (Fin.append Q (fun i => E i+c • D i)) F G)) := by
  have he (c : K) : (fun i => Fin.append Q E i+c • Fin.append 0 D i)=
      Fin.append Q (fun i => E i+c • D i) := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [Fin.append_left,Pi.zero_apply,smul_zero,add_zero]
    · intro j
      simp only [Fin.append_right]
  obtain ⟨R,hR,hr⟩ := background_pencil_rank_open (Fin.append Q E) (Fin.append 0 D) F G hi hu
  obtain ⟨c,hc,hgood,hex,hs⟩ := exists_actual_even_pencil_replacement Q F G E D s hex hs
    (P*R) (by simpa only [map_mul] using mul_ne_zero hP hR)
  have hgood' : eval (fun _ => c) P≠0 ∧ eval (fun _ => c) R≠0 := by
    simpa only [map_mul,mul_ne_zero_iff] using hgood
  have hri := hr c hgood'.2
  rw [he] at hri
  exact ⟨c,hc,hgood'.1,hex,hs,hri⟩

end Froberg
