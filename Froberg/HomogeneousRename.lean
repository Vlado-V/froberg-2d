import Froberg.FormalEmbedding
import Froberg.ComplementaryTargetDeletion

/-! Literal variable embeddings and deletion of the complementary old target. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] {m n d r : ℕ}

def renameForm (f : Fin m → Fin n) : Forms K m d →ₗ[K] Forms K n d where
  toFun p := ⟨rename f p.val,p.property.rename_isHomogeneous⟩
  map_add' a b := Subtype.ext (map_add (rename f) a.val b.val)
  map_smul' c a := Subtype.ext (by simp)

theorem renameForm_injective (f : Fin m ↪ Fin n) :
    Function.Injective (renameForm (K := K) (d := d) f) := by
  intro a b h
  apply Subtype.ext
  exact rename_injective f f.injective (congrArg Subtype.val h)

theorem renameForm_mulForm (f : Fin m → Fin n) (a b : Forms K m d) :
    renameForm f (mulForm a b)=mulForm (renameForm f a) (renameForm f b) :=
  Subtype.ext (map_mul (rename f) a.val b.val)

theorem renameForm_formal_multiplication (f : Fin m → Fin n) :
    (formalPolynomialMultiplication (K := K) (n := n) (d := d)).comp
        (SymmetricFunctor.map (renameForm f))=
      (renameForm f).comp (formalPolynomialMultiplication (K := K) (n := m) (d := d)) := by
  apply LinearMap.ext
  intro x
  induction x using symmetricSquare_induction with
  | hprod a b =>
      simp only [LinearMap.comp_apply,symmetricMap_symProd,formalPolynomialMultiplication_symProd,
        renameForm_mulForm]
  | hzero => simp
  | hadd a b ha hb => simp only [map_add,ha,hb]
  | hsmul c a ha => simp only [map_smul,ha]

theorem exists_old_target_deletion (f : Fin m ↪ Fin n) (q : Fin r → Forms K m d) :
    ∃ Z : Submodule K (Forms K n (2*d)),
      finrank K Z=finrank K (EndpointQuotient K m d
        (Submodule.span K (Set.range (fun i => (q i).val)))) ∧
      Set.InjOn (Z.mkQ.comp (renameForm f)) (endpointMultiplication q).range ∧
      (renameForm (K := K) (d := 2*d) f).range.map Z.mkQ=
        ((endpointMultiplication q).range.map (renameForm f)).map Z.mkQ := by
  obtain ⟨Z,hZ,hinj,hfill⟩ := exists_complementary_target_deletion
    (renameForm (K := K) (d := 2*d) f) (renameForm_injective f) (endpointMultiplication q).range
  refine ⟨Z,?_,?_,hfill⟩
  · rwa [range_endpointMultiplication] at hZ
  · intro a ha b hb hab
    apply renameForm_injective f
    exact hinj ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩ hab

variable {Z : Type*} [AddCommGroup Z] [Module K Z]

theorem renamed_old_homology_finrank (htwo : (2 : K) ≠ 0)
    (q : Fin r → Forms K m d) (hq : LinearIndependent K q) (f : Fin m ↪ Fin n)
    (pi : Forms K n (2*d) →ₗ[K] Z)
    (hinj : Set.InjOn (pi.comp (renameForm f)) (endpointMultiplication q).range) :
    finrank K ((pi.comp formalPolynomialMultiplication).ker ⊓
      formalProducts ((Submodule.span K (Set.range q)).map (renameForm f)) (renameForm f).range :
        Submodule K (SymmetricSquare K (Forms K n d))) = finrank K (EndpointHomology q) := by
  apply embedded_old_homology_finrank htwo q hq (renameForm f) (renameForm_injective f)
    pi (pi.comp (renameForm f))
  · rw [LinearMap.comp_assoc,renameForm_formal_multiplication,← LinearMap.comp_assoc]
  · exact hinj

end Froberg
