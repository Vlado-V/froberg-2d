import Froberg.SymmetricIndependence
import Froberg.Graded

/-! Literal quadratic products of coordinate linear forms are independent. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] {h L : ℕ}

def coordinateLinearForms (hL : L≤h) : Fin L → Forms K h 1 :=
  fun i => ⟨X (Fin.castLE hL i),isHomogeneous_X _ _⟩

def quadraticPairForms (o : Fin L → Forms K h 1) : Sym2 (Fin L) → Forms K h 2 :=
  Sym2.lift ⟨fun i j => mulForm (o i) (o j),fun i j => Subtype.ext (mul_comm _ _)⟩

@[simp] theorem quadraticPairForms_val (o : Fin L → Forms K h 1) (p : Sym2 (Fin L)) :
    (quadraticPairForms o p).val=pairProducts (fun i => (o i).val) p := by
  induction p using Sym2.inductionOn with
  | _ i j => rfl

theorem coordinateLinearForms_pairProducts_independent (hL : L≤h) :
    LinearIndependent K (pairProducts (fun i => (coordinateLinearForms (K := K) hL i).val)) := by
  have hh := (linearIndependent_pairProducts_X (K := K) (ι := Fin L)).map'
    (rename (Fin.castLE hL)).toLinearMap
    (LinearMap.ker_eq_bot.mpr (rename_injective _ (Fin.castLE_injective hL)))
  convert hh using 1
  funext p
  induction p using Sym2.inductionOn with
  | _ i j => simp only [pairProducts_mk,Function.comp_apply,AlgHom.toLinearMap_apply,
      map_mul,rename_X,coordinateLinearForms]

theorem quadraticPairForms_independent (o : Fin L → Forms K h 1)
    (ho : LinearIndependent K (pairProducts (fun i => (o i).val))) :
    LinearIndependent K (quadraticPairForms o) := by
  apply LinearIndependent.of_comp (Forms K h 2).subtype
  simpa only [Function.comp_def,Submodule.subtype_apply,quadraticPairForms_val] using ho

theorem quadraticPairForms_span_finrank (o : Fin L → Forms K h 1)
    (ho : LinearIndependent K (pairProducts (fun i => (o i).val))) :
    finrank K (Submodule.span K (Set.range (quadraticPairForms o)))=(L+1).choose 2 := by
  rw [finrank_span_eq_card (quadraticPairForms_independent o ho),Sym2.card,Fintype.card_fin]

end Froberg
