module

public import Froberg.TypedPrivateQuadraticWitness
public import Froberg.DetectedBiformSeparation
public import Froberg.PreparedCoreExtension

@[expose] public section

/-! Extending the detected outer family across private scalar variables gives
an actual finite C.2 witness with fixed private columns. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct PrivateColumns
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ]
variable {a z n R s d b q h c f : ℕ}

/-- Adjoin scalar variables without changing any biform coefficient. -/
def fullBiformCoreExtension (z : ℕ) :
    FullBiform K σ a R s →ₗ[K] FullBiform K σ (a+z) R s where
  toFun p := ⟨rename (Sum.map id (Fin.castAdd z)) p.val,
    biformImage_core_extension (homogeneousSubmodule σ K R) p.property⟩
  map_add' p r := Subtype.ext (map_add _ _ _)
  map_smul' c p := Subtype.ext (map_smul (rename (Sum.map id (Fin.castAdd z))).toLinearMap c _)

@[simp] theorem fullBiformCoreExtension_val (p : FullBiform K σ a R s) :
    (fullBiformCoreExtension z p).val=rename (Sum.map id (Fin.castAdd z)) p.val := rfl

theorem fullBiformCoreExtension_injective :
    Function.Injective (fullBiformCoreExtension (K := K) (σ := σ) (a := a) (R := R) (s := s) z) := by
  intro p r he
  apply Subtype.ext
  exact rename_injective (Sum.map id (Fin.castAdd z))
    (Function.Injective.sumMap Function.injective_id (Fin.castAdd_injective a z))
    (congrArg Subtype.val he)

omit [Fintype σ] in
/-- Scalar renaming commutes with any output detector. -/
theorem biformVectorDetector_scalar_rename
    (T : MvPolynomial σ K →ₗ[K] (Fin c → K)) (g : Fin a → Fin n)
    (p : MvPolynomial (σ ⊕ Fin a) K) (k : Fin c) :
    biformVectorDetector T (rename (Sum.map id g) p) k=
      rename g (biformVectorDetector T p k) := by
  obtain ⟨v,rfl⟩ := (tensorEquivSum K σ (Fin a) K).surjective p
  induction v using TensorProduct.inductionOn with
  | tmul x y =>
    rw [tensorEquivSum_tmul]
    have he : rename (Sum.map id g) (rename Sum.inl x*rename Sum.inr y)=
        rename Sum.inl x*rename Sum.inr (rename g y) := by
      simp only [map_mul,rename_rename]
      rfl
    rw [he,biformVectorDetector_tmul,biformVectorDetector_tmul,map_smul]
  | add x y hx hy =>
    simpa only [map_add,Pi.add_apply] using congrArg₂ HAdd.hAdd hx hy

/-- The extended outer product row is literally the renamed core row. -/
theorem detectedSymmetricProductRow_core_extension
    (T : MvPolynomial σ K →ₗ[K] (Fin c → K))
    (F : Fin f → FullBiform K σ a R s) :
    detectedSymmetricProductRow (FullBiform K σ (a+z) R s).subtype
      (biformVectorDetector T) (fun i => fullBiformCoreExtension z (F i))=
      coreVectorExtension.comp
        (detectedSymmetricProductRow (FullBiform K σ a R s).subtype
          (biformVectorDetector T) F) := by
  have hpair (p : Sym2 (Fin f)) :
      pairProducts (fun i => (fullBiformCoreExtension z (F i)).val) p=
      rename (Sum.map id (Fin.castAdd z)) (pairProducts (fun i => (F i).val) p) := by
    induction p using Sym2.inductionOn with
    | _ i j => simp only [pairProducts_mk,fullBiformCoreExtension_val,map_mul]
  apply LinearMap.ext
  intro x
  funext k
  simp only [detectedSymmetricProductRow,LinearMap.coe_mk,AddHom.coe_mk,
    LinearMap.comp_apply,coreVectorExtension,LinearMap.pi_apply,LinearMap.proj_apply,
    AlgHom.toLinearMap_apply,Finset.sum_apply,Pi.smul_apply,map_sum,map_smul,
    Submodule.subtype_apply,hpair,biformVectorDetector_scalar_rename]

/-- Core scalar/outer separation survives the addition of private variables
and the fixed private nuisance block. -/
theorem typed_private_quadratic_extended_products_separation (hd : 3≤d)
    (bo : Basis (Fin h) K (homogeneousSubmodule σ K 1))
    (T : MvPolynomial σ K →ₗ[K] (Fin c → K))
    (w : Fin b → Fin h → K) (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (hA : ∀ i j,T (outputCombination (fun k => (bo k).val) (w i)*(bo j).val)=A i (Pi.single j 1))
    (P : Fin b → FullBiform K σ (a+z) 1 (d-1))
    (hP : ∀ i,(P i).val=rename Sum.inl (outputCombination (fun k => (bo k).val) (w i))*
      rename Sum.inr (monomial (privateExponent a (d-1) ι i) (1:K)))
    (Q : Fin q → Forms K a d) (F : Fin f → FullBiform K σ a 1 (d-1))
    (hF : ∀ (x : Fin q → Fin c → Forms K a (d-2)) (v : Sym2 (Fin f) → K),
      scalarCoefficientRow Q x+detectedSymmetricProductRow
        (FullBiform K σ a 1 (d-1)).subtype (biformVectorDetector T) F v=0 → v=0)
    (x : (Fin q → Fin c → Forms K (a+z) (d-2)) ×
      (Fin b → FullBiform K σ (a+z) 1 (d-1))) (v : Sym2 (Fin f) → K)
    (hrel : quadraticNuisanceRow (t := d-2)
      (FullBiform K σ (a+z) 1 (d-1)).subtype (biformVectorDetector T)
      (fun i => renameForm (Fin.castAdd z) (Q i)) P x+
      detectedSymmetricProductRow (FullBiform K σ (a+z) 1 (d-1)).subtype
        (biformVectorDetector T) (fun i => fullBiformCoreExtension z (F i)) v=0) : v=0 := by
  rw [detectedSymmetricProductRow_core_extension,LinearMap.comp_apply] at hrel
  exact (typed_private_quadratic_row_separation hd bo T w ι A hA P hP Q
    (detectedSymmetricProductRow (FullBiform K σ a 1 (d-1)).subtype
      (biformVectorDetector T) F) hF x v hrel).1

/-- The finite C.2 witness uses the supplied scalar and private families and
chooses its actual outer family internally from the paired coefficient space. -/
theorem exists_typed_private_quadratic_witness {H : ℕ}
    {I : Type*} [Fintype I] [DecidableEq I] (hd : 3≤d)
    (bo : Basis (Fin h) K (Forms K H 1))
    (T : Poly K H →ₗ[K] (Fin c → K))
    (w : Fin b → Fin h → K) (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (hA : ∀ i j,T (outputCombination (fun k => (bo k).val) (w i)*(bo j).val)=A i (Pi.single j 1))
    (hker : (privatePolynomialMap (a := a) (s := d-1) ι A).ker=
      Submodule.span K (Set.range (koszulVector (privateGenerator (a := a) (s := d-1) ι w))))
    (P : Fin b → FullBiform K (Fin H) (a+z) 1 (d-1))
    (hP : ∀ i,(P i).val=rename Sum.inl (outputCombination (fun k => (bo k).val) (w i))*
      rename Sum.inr (monomial (privateExponent a (d-1) ι i) (1:K)))
    (Q : Fin q → Forms K a d)
    (hQ : ∀ t,t≤d-2 → Function.Injective (prefixMultiplication Q t))
    (o : I → Forms K H 1)
    (ho : LinearIndependent K (fun p => T (pairProducts (fun i => (o i).val) p)))
    (C : Submodule K (Poly K a)) (hCdeg : C≤Forms K a (d-1))
    (hC : Function.Injective (subspaceSymmetricMultiplication C))
    (hCQ : Disjoint (C*C) (familySpace Q*Forms K a (d-2)))
    (hf : f≤Fintype.card I*(finrank K C/2)) :
    ∃ F : Fin f → FullBiform K (Fin H) (a+z) 1 (d-1),
      LinearIndependent K F ∧
      (quadraticNuisanceRow (t := d-2)
        (FullBiform K (Fin H) (a+z) 1 (d-1)).subtype (biformVectorDetector T)
        (fun i => renameForm (Fin.castAdd z) (Q i)) P).ker=
        (quadraticNuisanceBoundary (q := q) (c := c) (n := a+z) (t := d-2) P).range ∧
      ∀ (x : (Fin q → Fin c → Forms K (a+z) (d-2)) ×
        (Fin b → FullBiform K (Fin H) (a+z) 1 (d-1))) (v : Sym2 (Fin f) → K),
        quadraticNuisanceRow (t := d-2)
          (FullBiform K (Fin H) (a+z) 1 (d-1)).subtype (biformVectorDetector T)
          (fun i => renameForm (Fin.castAdd z) (Q i)) P x+
        detectedSymmetricProductRow (FullBiform K (Fin H) (a+z) 1 (d-1)).subtype
          (biformVectorDetector T) F v=0 → v=0 := by
  obtain ⟨F,hFi,hF⟩ := exists_scalar_separated_biform_family Q o T ho C hCdeg hC hCQ hf
  refine ⟨fun i => fullBiformCoreExtension z (F i),?_,
    typed_private_quadratic_row_exact hd bo T w ι A hA hker P hP Q hQ,?_⟩
  · exact hFi.map' (fullBiformCoreExtension z)
      (LinearMap.ker_eq_bot.mpr fullBiformCoreExtension_injective)
  · exact typed_private_quadratic_extended_products_separation hd bo T w ι A hA P hP Q F hF

end Froberg
