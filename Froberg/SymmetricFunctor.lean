import Mathlib.LinearAlgebra.TensorPower.Symmetric
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Functorial maps on mathlib's actual quotient construction of symmetric tensor powers. -/
noncomputable section
open TensorProduct
namespace Froberg.SymmetricFunctor

universe u v w z
variable {R ι : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]
variable {P : Type z} [AddCommMonoid P] [Module R P]

private theorem map_relation (f : M →ₗ[R] N) (x y : ⨂[R] (_ : ι), M)
    (h : addConGen (SymmetricPower.Rel R ι M) x y) :
    addConGen (SymmetricPower.Rel R ι N)
      (PiTensorProduct.map (fun _ : ι => f) x) (PiTensorProduct.map (fun _ : ι => f) y) := by
  induction h with
  | of x y h =>
    cases h with
    | perm e v =>
      change AddConGen.Rel (SymmetricPower.Rel R ι N) _ _
      simpa only [PiTensorProduct.map_tprod] using
        AddConGen.Rel.of _ _ (SymmetricPower.Rel.perm (R := R) e (fun i => f (v i)))
  | refl => exact AddCon.refl _ _
  | symm => apply AddCon.symm; assumption
  | trans => apply AddCon.trans <;> assumption
  | add =>
    simp only [map_add]
    apply AddCon.add <;> assumption

/-- A linear map induces a linear map of symmetric tensor powers. -/
def map (f : M →ₗ[R] N) : Sym[R] ι M →ₗ[R] Sym[R] ι N where
  __ := AddCon.lift _
    (((SymmetricPower.mk R ι N).comp (PiTensorProduct.map (fun _ : ι => f))).toAddMonoidHom)
    (fun x y h => Quotient.sound (map_relation f x y h))
  map_smul' r x := AddCon.induction_on x fun x => by
    change SymmetricPower.mk R ι N (PiTensorProduct.map (fun _ : ι => f) (r • x)) =
      r • SymmetricPower.mk R ι N (PiTensorProduct.map (fun _ : ι => f) x)
    rw [map_smul, map_smul]

@[simp] theorem map_mk (f : M →ₗ[R] N) (x : ⨂[R] (_ : ι), M) :
    map (ι := ι) f (SymmetricPower.mk R ι M x) =
      SymmetricPower.mk R ι N (PiTensorProduct.map (fun _ : ι => f) x) := rfl

@[simp] theorem map_tprod (f : M →ₗ[R] N) (x : ι → M) :
    map f (SymmetricPower.tprod R x) = SymmetricPower.tprod R (fun i => f (x i)) := by
  change map f (SymmetricPower.mk R ι M (PiTensorProduct.tprod R x)) = _
  rw [map_mk, PiTensorProduct.map_tprod]
  rfl

@[simp] theorem map_id : map (ι := ι) (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  ext x
  refine AddCon.induction_on x fun x => ?_
  change SymmetricPower.mk R ι M (PiTensorProduct.map (fun _ : ι => LinearMap.id) x) =
    SymmetricPower.mk R ι M x
  rw [PiTensorProduct.map_id, LinearMap.id_apply]

@[simp] theorem map_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    map (ι := ι) (g.comp f) = (map g).comp (map f) := by
  ext x
  refine AddCon.induction_on x fun x => ?_
  change SymmetricPower.mk R ι P (PiTensorProduct.map (fun _ : ι => g.comp f) x) =
    SymmetricPower.mk R ι P
      (PiTensorProduct.map (fun _ : ι => g) (PiTensorProduct.map (fun _ : ι => f) x))
  rw [PiTensorProduct.map_comp, LinearMap.comp_apply]

/-- A linear retraction remains a retraction on symmetric powers. -/
theorem map_leftInverse (f : M →ₗ[R] N) (g : N →ₗ[R] M) (h : g.comp f = LinearMap.id) :
    Function.LeftInverse (map (ι := ι) g) (map (ι := ι) f) := by
  intro x
  have hmap := congrArg (fun k : M →ₗ[R] M => map (ι := ι) k) h
  rw [map_comp, map_id] at hmap
  exact LinearMap.congr_fun hmap x

/-- In particular, split injections induce injective maps of symmetric powers. -/
theorem map_injective_of_retraction (f : M →ₗ[R] N) (g : N →ₗ[R] M)
    (h : g.comp f = LinearMap.id) : Function.Injective (map (ι := ι) f) :=
  (map_leftInverse f g h).injective

/-- Over a field, every injective linear map induces an injection on symmetric powers. -/
theorem map_injective {K : Type u} [Field K]
    {E : Type v} [AddCommGroup E] [Module K E]
    {F : Type w} [AddCommGroup F] [Module K F]
    (f : E →ₗ[K] F) (hf : Function.Injective f) :
    Function.Injective (map (ι := ι) f) := by
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  exact map_injective_of_retraction f g hg

end Froberg.SymmetricFunctor
