module

public import Quartic.HomogeneousCoefficientCoordinates
public import Quartic.BilinearScalarExtension
public import Froberg.OuterMultiplication
public import Quartic.PolynomialBilinearCoordinates

@[expose] public section

/-!
# Field-compatible coordinates for actual row multiplication

All coordinate positions are monomials and row labels, independent of K.
Scalar extension therefore preserves the actual multiplication tensor.
-/
noncomputable section
namespace Froberg.VectorMultiplicationCoordinates
open Module MvPolynomial Quartic.HomogeneousCoefficientCoordinates
open Quartic
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {h m s d : ℕ}

abbrev Rows (K : Type*) [Field K] (h m d : ℕ) := Fin h → Forms K m d
abbrev RowIndex (h m d : ℕ) := Fin h × Exponent m d
abbrev FormCount (m d : ℕ) := @Fintype.card (Exponent m d) (exponentFintype m d)
abbrev RowCount (h m d : ℕ) := Fintype.card (RowIndex h m d)

def rowEquiv : Rows K h m d ≃ₗ[K] (RowIndex h m d → K) where
  toFun v i := equiv (v i.1) i.2
  invFun x r := equiv.symm (fun e => x (r,e))
  left_inv v := by funext r; exact equiv.symm_apply_apply (v r)
  right_inv x := by funext i; exact congrFun (equiv.apply_symm_apply (fun e => x (i.1,e))) i.2
  map_add' _ _ := by funext i; exact congrFun (equiv.map_add _ _) i.2
  map_smul' _ _ := by funext i; exact congrFun (equiv.map_smul _ _) i.2

def rowFiniteEquiv : Rows K h m d ≃ₗ[K] (Fin (RowCount h m d) → K) :=
  rowEquiv.trans (reindex (RowIndex h m d))

def mapRows (v : Rows K h m d) : Rows L h m d := fun r => mapForm (v r)

@[simp] theorem rowEquiv_mapRows (v : Rows K h m d) (i : RowIndex h m d) :
    rowEquiv (mapRows (L := L) v) i = algebraMap K L (rowEquiv v i) :=
  equiv_mapForm _ _

@[simp] theorem rowFiniteEquiv_mapRows (v : Rows K h m d) (i : Fin (RowCount h m d)) :
    rowFiniteEquiv (mapRows (L := L) v) i = algebraMap K L (rowFiniteEquiv v i) :=
  rowEquiv_mapRows _ _

theorem mapForm_finiteEquiv_symm (x : Fin (FormCount m d) → K) :
    mapForm (L := L) (finiteEquiv.symm x) = finiteEquiv.symm (fun i => algebraMap K L (x i)) := by
  apply finiteEquiv.injective
  funext i
  rw [finiteEquiv_mapForm,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]

theorem mapRows_rowFiniteEquiv_symm (x : Fin (RowCount h m d) → K) :
    mapRows (L := L) (rowFiniteEquiv.symm x) = rowFiniteEquiv.symm (fun i => algebraMap K L (x i)) := by
  apply rowFiniteEquiv.injective
  funext i
  rw [rowFiniteEquiv_mapRows,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]

/-- The fixed multiplication underlying every mixed presentation. -/
def multiplication : Forms K m d →ₗ[K] Rows K h m s →ₗ[K] Rows K h m (s+d) :=
  AttachedMultiplication.vectorMultiply

@[simp] theorem multiplication_val (f : Forms K m d) (v : Rows K h m s) (r : Fin h) :
    (multiplication f v r).val = f.val*(v r).val := rfl

theorem mapRows_multiplication (f : Forms K m d) (v : Rows K h m s) :
    mapRows (L := L) (multiplication f v) = multiplication (mapForm f) (mapRows v) := by
  funext r
  apply Subtype.ext
  exact map_mul (MvPolynomial.map (algebraMap K L)) _ _

/-- The actual bilinear multiplication written in the fixed monomial coordinates. -/
def coordinate : (Fin (FormCount m d) → K) →ₗ[K]
    (Fin (RowCount h m s) → K) →ₗ[K] (Fin (RowCount h m (s+d)) → K) :=
  (PolynomialBilinearCoordinates.conjugate rowFiniteEquiv rowFiniteEquiv multiplication).comp
    finiteEquiv.symm.toLinearMap

@[simp] theorem coordinate_apply (f : Fin (FormCount m d) → K) (v : Fin (RowCount h m s) → K) :
    coordinate f v = rowFiniteEquiv (multiplication (finiteEquiv.symm f) (rowFiniteEquiv.symm v)) := rfl

/-- Multiplication commutes with coefficient-field extension in these coordinates. -/
theorem coordinate_map (f : Fin (FormCount m d) → K) (v : Fin (RowCount h m s) → K)
    (k : Fin (RowCount h m (s+d))) :
    coordinate (fun i => algebraMap K L (f i)) (fun i => algebraMap K L (v i)) k =
      algebraMap K L (coordinate f v k) := by
  rw [coordinate_apply, ← mapForm_finiteEquiv_symm, ← mapRows_rowFiniteEquiv_symm,
    ← mapRows_multiplication, rowFiniteEquiv_mapRows]
  rfl

/-- Scalar extension of the coefficient tensor is the actual multiplication over L. -/
theorem extend_coordinate : BilinearScalarExtension.extend (L := L) (coordinate (K := K) (h := h) (m := m) (s := s) (d := d)) =
    coordinate (K := L) (h := h) (m := m) (s := s) (d := d) := by
  classical
  apply (Pi.basisFun L (Fin (FormCount m d))).ext
  intro f
  apply (Pi.basisFun L (Fin (RowCount h m s))).ext
  intro v
  funext k
  simp only [Pi.basisFun_apply,BilinearScalarExtension.extend_basis]
  have hmap := coordinate_map (L := L) (Pi.single f (1 : K)) (Pi.single v (1 : K)) k
  have hf : (fun i : Fin (FormCount m d) => algebraMap K L
      ((Pi.single f (1 : K) : Fin (FormCount m d) → K) i)) =
      (Pi.single f (1 : L) : Fin (FormCount m d) → L) := by
    funext i
    simp [Pi.single_apply]
  have hv : (fun i : Fin (RowCount h m s) => algebraMap K L
      ((Pi.single v (1 : K) : Fin (RowCount h m s) → K) i)) =
      (Pi.single v (1 : L) : Fin (RowCount h m s) → L) := by
    funext i
    simp [Pi.single_apply]
  rw [hf,hv] at hmap
  exact hmap.symm

/-- Coordinate images are the actual images transported by the target equivalence. -/
theorem image_coordinate (S : Submodule K (Rows K h m s)) :
    BilinearImage.image (coordinate (d := d)) (S.map rowFiniteEquiv.toLinearMap) =
      (BilinearImage.image (multiplication (d := d)) S).map rowFiniteEquiv.toLinearMap := by
  apply le_antisymm
  · apply iSup_le
    intro f
    rintro _ ⟨v,⟨x,hx,rfl⟩,rfl⟩
    refine ⟨multiplication (finiteEquiv.symm f) x,
      BilinearImage.product_mem _ _ _ _ hx,?_⟩
    simp only [coordinate_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
  · apply Submodule.map_le_iff_le_comap.mpr
    apply iSup_le
    intro f
    rintro _ ⟨v,hv,rfl⟩
    have hp := BilinearImage.product_mem coordinate (S.map rowFiniteEquiv.toLinearMap)
      (finiteEquiv f) (rowFiniteEquiv v) ⟨v,hv,rfl⟩
    change rowFiniteEquiv (multiplication f v) ∈
      BilinearImage.image (coordinate (d := d)) (S.map rowFiniteEquiv.toLinearMap)
    simpa only [coordinate_apply,LinearEquiv.symm_apply_apply] using hp

theorem image_coordinate_finrank (S : Submodule K (Rows K h m s)) :
    finrank K (BilinearImage.image (coordinate (d := d)) (S.map rowFiniteEquiv.toLinearMap)) =
      finrank K (BilinearImage.image (multiplication (d := d)) S) := by
  rw [image_coordinate,LinearEquiv.finrank_map_eq]

end Froberg.VectorMultiplicationCoordinates
