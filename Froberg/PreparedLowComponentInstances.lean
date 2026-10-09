module

public import Froberg.PreparedTensorDetector
public import Froberg.PreparedBiformFamilies
public import Froberg.PreparedFamilyIndependence
public import Froberg.RestoredScalarCompatibility
public import Froberg.BackgroundFlagSpan

@[expose] public section

/-! Literal low-degree components of prepared and restored backgrounds.
The scalar space includes every scalar tail, while the linear space includes
only the private columns. Pure restoration terms disappear in degrees at most two. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
variable {K : Type} [Field K] {h m d : ℕ}

/-- It suffices to check low components on the displayed generators. -/
theorem PreparedLowComponents.span {I : Type*} (g : I → Forms K (h+m) d)
    (S P D : Submodule K (Poly K (h+m)))
    (hg : ∀ i, coreComponent h m 0 (g i).val ∈ S ∧
      coreComponent h m 1 (g i).val ∈ P ∧ coreComponent h m 2 (g i).val ∈ D) :
    PreparedLowComponents (Submodule.span K (Set.range g)) S P D := by
  have hmem (j : ℕ) (T : Submodule K (Poly K (h+m)))
      (hj : ∀ i,coreComponent h m j (g i).val∈T) :
      ∀ w : Forms K (h+m) d,w∈Submodule.span K (Set.range g) →
        coreComponent h m j w.val∈T := by
    intro w hw
    have hb : Submodule.span K (Set.range g) ≤
        T.comap ((coreComponent h m j).comp (Forms K (h+m) d).subtype) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact hj i
    exact hb hw
  exact ⟨hmem 0 S (fun i => (hg i).1),hmem 1 P (fun i => (hg i).2.1),
    hmem 2 D (fun i => (hg i).2.2)⟩

theorem PreparedLowComponents.sup
    {W W' : Submodule K (Forms K (h+m) d)}
    {S P D : Submodule K (Poly K (h+m))}
    (H : PreparedLowComponents W S P D) (H' : PreparedLowComponents W' S P D) :
    PreparedLowComponents (W ⊔ W') S P D := by
  have hmem (j : ℕ) (T : Submodule K (Poly K (h+m)))
      (hj : ∀ w : Forms K (h+m) d,w∈W → coreComponent h m j w.val∈T)
      (hj' : ∀ w : Forms K (h+m) d,w∈W' → coreComponent h m j w.val∈T) :
      ∀ w : Forms K (h+m) d,w∈W ⊔ W' → coreComponent h m j w.val∈T := by
    intro w hw
    obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp hw
    simpa only [Submodule.coe_add,map_add] using T.add_mem (hj x hx) (hj' y hy)
  exact ⟨hmem 0 S H.scalar H'.scalar,hmem 1 P H.linear H'.linear,
    hmem 2 D H.quadratic H'.quadratic⟩

/-- The two-block tensor image is the literal split-polynomial tensor image. -/
theorem rename_mem_polynomialTensorSpace
    (A : Submodule K (Poly K h)) (B : Submodule K (Poly K m))
    {p : MvPolynomial (Fin h ⊕ Fin m) K} (hp : p∈biformImage A B) :
    rename finSumFinEquiv p∈polynomialTensorSpace A B := by
  rcases hp with ⟨a,⟨z,rfl⟩,rfl⟩
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    refine ⟨x ⊗ₜ[K] y,?_⟩
    change polynomialTensorMap A B (x ⊗ₜ[K] y)=
      rename finSumFinEquiv (tensorEquivSum K (Fin h) (Fin m) K (x.val ⊗ₜ[K] y.val))
    rw [polynomialTensorMap_tmul,splitPolynomialEquiv_tmul,tensorEquivSum_tmul,
      map_mul,rename_rename,rename_rename]
    rfl
  | add x y hx hy =>
    simpa only [map_add] using (polynomialTensorSpace A B).add_mem hx hy

/-- Scalar tails use the degree-zero output factor. -/
theorem scalar_mem_polynomialTensorSpace (Q : Submodule K (Poly K m))
    {p : Poly K m} (hp : p∈Q) :
    rename (Fin.natAdd h) p∈polynomialTensorSpace (Forms K h 0) Q := by
  refine ⟨constantOneForm K h ⊗ₜ[K] (⟨p,hp⟩ : Q),?_⟩
  simp only [polynomialTensorMap_tmul,splitPolynomialEquiv_tmul,constantOneForm,
    map_one,one_mul]

/-- Block weight is preserved by the canonical enumeration of variables. -/
theorem core_weighted_rename {j : ℕ} {p : MvPolynomial (Fin h ⊕ Fin m) K}
    (hp : p.IsWeightedHomogeneous (blockWeight h m) j) :
    (rename finSumFinEquiv p).IsWeightedHomogeneous (coreWeight h m) j := by
  rw [coreWeight_eq_blockWeight]
  apply weighted_homogeneous_rename finSumFinEquiv.toEmbedding
  simpa only [Function.comp_def,Equiv.coe_toEmbedding,Equiv.symm_apply_apply] using hp

namespace PreparedTarget
open PreparedParameters
variable [Infinite K]
variable {q f u r : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (Poly K h)}

/-- All scalar slots, including the tails of positive prepared columns. -/
def preparedScalarSpace (p : PreparedParameters.Space m d q J counts O) :
    Submodule K (Poly K m) := Submodule.span K (Set.range (fun i => (p.1 i).val))

/-- The actual private linear pieces, with no outer columns included. -/
def preparedPrivateLinearSpace (P : OuterSpace K (Fin h) m d u) :
    Submodule K (Poly K (h+m)) :=
  Submodule.span K (Set.range (fun i => rename finSumFinEquiv (P i).val))

theorem renamed_prepared_low_components
    (hO : ∀ j∈J,O j≤Forms K h j) (hmin : ∀ j∈J,2≤j)
    (p : PreparedParameters.Space m d q J counts O) (i : PreparedParameters.Label q J counts) :
    coreComponent h m 0 (rename finSumFinEquiv (PreparedParameters.generator p i)) ∈
        polynomialTensorSpace (Forms K h 0) (preparedScalarSpace p) ∧
    coreComponent h m 1 (rename finSumFinEquiv (PreparedParameters.generator p i))=0 ∧
    coreComponent h m 2 (rename finSumFinEquiv (PreparedParameters.generator p i)) ∈
        polynomialTensorSpace (O 2) (Forms K m (d-2)) := by
  have hs := core_weighted_rename (scalar_weight p i)
  have hsmem : rename finSumFinEquiv (scalar p i)∈
      polynomialTensorSpace (Forms K h 0) (preparedScalarSpace p) := by
    change rename finSumFinEquiv (rename Sum.inr (p.1 i).val)∈_
    rw [rename_rename]
    exact scalar_mem_polynomialTensorSpace _ (Submodule.subset_span ⟨i,rfl⟩)
  have hh : coreComponent h m 0 (rename finSumFinEquiv (high p i))=0 ∧
      coreComponent h m 1 (rename finSumFinEquiv (high p i))=0 ∧
      coreComponent h m 2 (rename finSumFinEquiv (high p i))∈
        polynomialTensorSpace (O 2) (Forms K m (d-2)) := by
    cases i with
    | inl i => simp [high,coreComponent]
    | inr a =>
      have ha := hmin _ a.1.property
      have hw := core_weighted_rename (high_weight hO p (Sum.inr a))
      change (rename finSumFinEquiv (high p (Sum.inr a))).IsWeightedHomogeneous
        (coreWeight h m) a.1.val at hw
      refine ⟨hw.weightedHomogeneousComponent_ne 0 (by omega),
        hw.weightedHomogeneousComponent_ne 1 (by omega),?_⟩
      by_cases htwo : 2=a.1.val
      · change weightedHomogeneousComponent (coreWeight h m) 2 _∈_
        rw [weightedHomogeneousComponent_of_mem hw,ite_eq_left htwo]
        have hm := rename_mem_polynomialTensorSpace (O a.1.val) (Forms K m (d-a.1.val))
          (p.2 a.1 a.2).property
        simpa only [htwo,high,Sum.elim_inr] using hm
      · change weightedHomogeneousComponent (coreWeight h m) 2 _∈_
        rw [weightedHomogeneousComponent_of_mem hw,ite_eq_right htwo]
        exact Submodule.zero_mem _
  change _ ∧ _ ∧ _
  simp only [PreparedParameters.generator,map_add,coreComponent,
    hs.weightedHomogeneousComponent_same,
    hs.weightedHomogeneousComponent_ne 1 (by omega),
    hs.weightedHomogeneousComponent_ne 2 (by omega),
    show weightedHomogeneousComponent (coreWeight h m) 0 (rename finSumFinEquiv (high p i))=0 from hh.1,
    show weightedHomogeneousComponent (coreWeight h m) 1 (rename finSumFinEquiv (high p i))=0 from hh.2.1,
    add_zero,zero_add]
  exact ⟨hsmem,trivial,hh.2.2⟩

theorem renamed_private_low_components (hd : 3≤d)
    (U : Fin u → Forms K h d) (P : OuterSpace K (Fin h) m d u)
    (F : OuterSpace K (Fin h) m d f) (i : Fin u) :
    coreComponent h m 0 (rename finSumFinEquiv (oddGenerator U P F (Sum.inr i)))=0 ∧
    coreComponent h m 1 (rename finSumFinEquiv (oddGenerator U P F (Sum.inr i)))=
      rename finSumFinEquiv (P i).val ∧
    coreComponent h m 2 (rename finSumFinEquiv (oddGenerator U P F (Sum.inr i)))=0 := by
  have hl := core_weighted_rename (combinedLinear_weight P F (Sum.inr i))
  change (rename finSumFinEquiv (P i).val).IsWeightedHomogeneous (coreWeight h m) 1 at hl
  have hu := core_weighted_rename (combinedPure_weight (m := m) U (Sum.inr (α := Fin f) i))
  change _ ∧ _ ∧ _
  simp only [oddGenerator,Pi.add_apply,map_add,coreComponent,
    hl.weightedHomogeneousComponent_ne 0 (by omega),
    hl.weightedHomogeneousComponent_same,
    hl.weightedHomogeneousComponent_ne 2 (by omega),
    hu.weightedHomogeneousComponent_ne 0 (by omega),
    hu.weightedHomogeneousComponent_ne 1 (by omega),
    hu.weightedHomogeneousComponent_ne 2 (by omega),add_zero,
    combinedLinear,Sum.elim_inr]
  exact ⟨trivial,trivial,trivial⟩

/-- The literal prepared private background has exactly the required low pieces. -/
theorem prepared_private_background_lowComponents (hd : 3≤d) (ho : d%2=1)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d)
    (heven : ∀ j∈J,j%2=0) (hmin : ∀ j∈J,2≤j)
    (U : Fin u → Forms K h d) (P : OuterSpace K (Fin h) m d u)
    (F : OuterSpace K (Fin h) m d f) (p : PreparedParameters.Space m d q J counts O) :
    PreparedLowComponents
      (embeddedFlagSpace (renameForm (Fin.natAdd h)) (fun i : Fin q => p.1 (Sum.inl i)) ⊔
        Submodule.span K (Set.range (backgroundPositiveForms
          (preparedPositiveBiform hO hJ heven p)
          (fun i => preparedOddBiform (by omega) ho U P F (Sum.inr i)))))
      (polynomialTensorSpace (Forms K h 0) (preparedScalarSpace p))
      (preparedPrivateLinearSpace P) (polynomialTensorSpace (O 2) (Forms K m (d-2))) := by
  apply PreparedLowComponents.sup
  · unfold embeddedFlagSpace
    rw [Submodule.map_span,←Set.range_comp]
    apply PreparedLowComponents.span
    intro i
    have hh := renamed_prepared_low_components hO hmin p (Sum.inl i)
    have he : (renameForm (Fin.natAdd h) (p.1 (Sum.inl i))).val=
        rename finSumFinEquiv (PreparedParameters.generator p (Sum.inl i)) := by
      change rename (Fin.natAdd h) (p.1 (Sum.inl i)).val=
        rename finSumFinEquiv (rename Sum.inr (p.1 (Sum.inl i)).val+0)
      rw [add_zero,rename_rename]
      rfl
    change coreComponent h m 0 (renameForm (Fin.natAdd h) (p.1 (Sum.inl i))).val∈_ ∧
      coreComponent h m 1 (renameForm (Fin.natAdd h) (p.1 (Sum.inl i))).val∈_ ∧
      coreComponent h m 2 (renameForm (Fin.natAdd h) (p.1 (Sum.inl i))).val∈_
    rw [he]
    exact ⟨hh.1,hh.2.1 ▸ Submodule.zero_mem _,hh.2.2⟩
  · apply PreparedLowComponents.span
    intro i
    cases i with
    | inl i =>
      have hh := renamed_prepared_low_components hO hmin p (Sum.inr ((Fintype.equivFin _).symm i))
      exact ⟨hh.1,hh.2.1 ▸ Submodule.zero_mem _,hh.2.2⟩
    | inr i =>
      have hh := renamed_private_low_components hd U P F i
      exact ⟨hh.1 ▸ Submodule.zero_mem _,hh.2.1 ▸ Submodule.subset_span ⟨i,rfl⟩,
        hh.2.2 ▸ Submodule.zero_mem _⟩

/-- Pure restoration changes none of the three low components. -/
theorem renamed_restored_low_components (hd : 3≤d) (he : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d)
    (heven : ∀ j∈J,j%2=0) (hmin : ∀ j∈J,2≤j)
    (idx : Fin r ≃ PreparedParameters.Label q J counts)
    (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredSpace m d q J counts O) (i : Fin r) :
    coreComponent h m 0 (rename finSumFinEquiv
        (restoredFamilyLinear he hO hJ heven idx slot p i).val)∈
      polynomialTensorSpace (Forms K h 0) (preparedScalarSpace p.1) ∧
    coreComponent h m 1 (rename finSumFinEquiv
        (restoredFamilyLinear he hO hJ heven idx slot p i).val)=0 ∧
    coreComponent h m 2 (rename finSumFinEquiv
        (restoredFamilyLinear he hO hJ heven idx slot p i).val)∈
      polynomialTensorSpace (O 2) (Forms K m (d-2)) := by
  have hh := renamed_prepared_low_components hO hmin p.1 (idx i)
  have hu := core_weighted_rename (pureShift_weight (m := m) he slot p.2 i)
  change
    coreComponent h m 0 (rename finSumFinEquiv (PreparedParameters.generator p.1 (idx i)+
        (PolynomialRestoration.pureShift (pureEvenEmbed he) slot p.2 i).val))∈_ ∧
    coreComponent h m 1 (rename finSumFinEquiv (PreparedParameters.generator p.1 (idx i)+
        (PolynomialRestoration.pureShift (pureEvenEmbed he) slot p.2 i).val))=0 ∧
    coreComponent h m 2 (rename finSumFinEquiv (PreparedParameters.generator p.1 (idx i)+
        (PolynomialRestoration.pureShift (pureEvenEmbed he) slot p.2 i).val))∈_
  simpa only [map_add,coreComponent,
    hu.weightedHomogeneousComponent_ne 0 (by omega),
    hu.weightedHomogeneousComponent_ne 1 (by omega),
    hu.weightedHomogeneousComponent_ne 2 (by omega),add_zero] using hh

/-- The restored even background has no linear piece and retains its original
scalar and constrained quadratic pieces. The outer family remains separate. -/
theorem restored_background_lowComponents (hd : 3≤d) (he : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d)
    (heven : ∀ j∈J,j%2=0) (hmin : ∀ j∈J,2≤j)
    (idx : Fin r ≃ PreparedParameters.Label q J counts)
    (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredSpace m d q J counts O) :
    PreparedLowComponents
      (embeddedFlagSpace (renameForm (Fin.natAdd h)) (fun i : Fin q => p.1.1 (Sum.inl i)) ⊔
        Submodule.span K (Set.range (backgroundPositiveForms
          (restoredPositiveBiform he hO hJ heven idx slot p) emptyOddFamily)))
      (polynomialTensorSpace (Forms K h 0) (preparedScalarSpace p.1))
      ⊥ (polynomialTensorSpace (O 2) (Forms K m (d-2))) := by
  apply PreparedLowComponents.sup
  · unfold embeddedFlagSpace
    rw [Submodule.map_span,←Set.range_comp]
    apply PreparedLowComponents.span
    intro i
    have hh := renamed_prepared_low_components hO hmin p.1 (Sum.inl i)
    have hval : (renameForm (Fin.natAdd h) (p.1.1 (Sum.inl i))).val=
        rename finSumFinEquiv (PreparedParameters.generator p.1 (Sum.inl i)) := by
      change rename (Fin.natAdd h) (p.1.1 (Sum.inl i)).val=
        rename finSumFinEquiv (rename Sum.inr (p.1.1 (Sum.inl i)).val+0)
      rw [add_zero,rename_rename]
      rfl
    change coreComponent h m 0 (renameForm (Fin.natAdd h) (p.1.1 (Sum.inl i))).val∈_ ∧
      coreComponent h m 1 (renameForm (Fin.natAdd h) (p.1.1 (Sum.inl i))).val∈_ ∧
      coreComponent h m 2 (renameForm (Fin.natAdd h) (p.1.1 (Sum.inl i))).val∈_
    rw [hval]
    exact ⟨hh.1,hh.2.1,hh.2.2⟩
  · apply PreparedLowComponents.span
    intro i
    cases i with
    | inl i =>
      have hh := renamed_restored_low_components hd he hO hJ heven hmin idx slot p
        (idx.symm (Sum.inr ((Fintype.equivFin _).symm i)))
      exact ⟨hh.1,hh.2.1,hh.2.2⟩
    | inr i => exact Fin.elim0 i

end PreparedTarget
end Froberg
