module

public import Quartic.HomogeneousCoefficientCoordinates
public import Quartic.BilinearScalarExtension
public import Quartic.ConvolutionAmbientImage
public import Quartic.PolynomialBilinearCoordinates

@[expose] public section

/-!
# Field-compatible coordinates for actual row multiplication

All coordinate positions are monomials and row labels, independent of K.
Scalar extension therefore preserves the actual multiplication tensor.
-/
noncomputable section
namespace Quartic.RowMultiplicationCoordinates
open Module MvPolynomial HomogeneousCoefficientCoordinates
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {m d : ℕ}

abbrev Rows (K : Type*) [Field K] (m d : ℕ) := Fin 3 → Forms K m d
abbrev RowIndex (m d : ℕ) := Fin 3 × Exponent m d
abbrev FormCount (m d : ℕ) := @Fintype.card (Exponent m d) (exponentFintype m d)
abbrev RowCount (m d : ℕ) := Fintype.card (RowIndex m d)

def rowEquiv : Rows K m d ≃ₗ[K] (RowIndex m d → K) where
  toFun v i := equiv (v i.1) i.2
  invFun x r := equiv.symm (fun e => x (r,e))
  left_inv v := by funext r; exact equiv.symm_apply_apply (v r)
  right_inv x := by funext i; exact congrFun (equiv.apply_symm_apply (fun e => x (i.1,e))) i.2
  map_add' _ _ := by funext i; exact congrFun (equiv.map_add _ _) i.2
  map_smul' _ _ := by funext i; exact congrFun (equiv.map_smul _ _) i.2

def rowFiniteEquiv : Rows K m d ≃ₗ[K] (Fin (RowCount m d) → K) :=
  rowEquiv.trans (reindex (RowIndex m d))

def mapRows (v : Rows K m d) : Rows L m d := fun r => mapForm (v r)

@[simp] theorem rowEquiv_mapRows (v : Rows K m d) (i : RowIndex m d) :
    rowEquiv (mapRows (L := L) v) i = algebraMap K L (rowEquiv v i) :=
  equiv_mapForm _ _

@[simp] theorem rowFiniteEquiv_mapRows (v : Rows K m d) (i : Fin (RowCount m d)) :
    rowFiniteEquiv (mapRows (L := L) v) i = algebraMap K L (rowFiniteEquiv v i) :=
  rowEquiv_mapRows _ _

theorem mapForm_finiteEquiv_symm (x : Fin (FormCount m d) → K) :
    mapForm (L := L) (finiteEquiv.symm x) = finiteEquiv.symm (fun i => algebraMap K L (x i)) := by
  apply finiteEquiv.injective
  funext i
  rw [finiteEquiv_mapForm,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]

theorem mapRows_rowFiniteEquiv_symm (x : Fin (RowCount m d) → K) :
    mapRows (L := L) (rowFiniteEquiv.symm x) = rowFiniteEquiv.symm (fun i => algebraMap K L (x i)) := by
  apply rowFiniteEquiv.injective
  funext i
  rw [rowFiniteEquiv_mapRows,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]

/-- The fixed multiplication underlying every mixed presentation. -/
def multiplication : Forms K m 2 →ₗ[K] Rows K m 1 →ₗ[K] Rows K m 3 :=
  ConvolutionAmbientImage.multiplication (t := m) (w := 0)

@[simp] theorem multiplication_val (f : Forms K m 2) (v : Rows K m 1) (r : Fin 3) :
    (multiplication f v r).val = f.val*(v r).val := rfl

theorem mapRows_multiplication (f : Forms K m 2) (v : Rows K m 1) :
    mapRows (L := L) (multiplication f v) = multiplication (mapForm f) (mapRows v) := by
  funext r
  apply Subtype.ext
  exact map_mul (MvPolynomial.map (algebraMap K L)) _ _

/-- The actual bilinear multiplication written in the fixed monomial coordinates. -/
def coordinate : (Fin (FormCount m 2) → K) →ₗ[K]
    (Fin (RowCount m 1) → K) →ₗ[K] (Fin (RowCount m 3) → K) :=
  (PolynomialBilinearCoordinates.conjugate rowFiniteEquiv rowFiniteEquiv multiplication).comp
    finiteEquiv.symm.toLinearMap

@[simp] theorem coordinate_apply (f : Fin (FormCount m 2) → K) (v : Fin (RowCount m 1) → K) :
    coordinate f v = rowFiniteEquiv (multiplication (finiteEquiv.symm f) (rowFiniteEquiv.symm v)) := rfl

/-- Multiplication commutes with coefficient-field extension in these coordinates. -/
theorem coordinate_map (f : Fin (FormCount m 2) → K) (v : Fin (RowCount m 1) → K)
    (k : Fin (RowCount m 3)) :
    coordinate (fun i => algebraMap K L (f i)) (fun i => algebraMap K L (v i)) k =
      algebraMap K L (coordinate f v k) := by
  rw [coordinate_apply, ← mapForm_finiteEquiv_symm, ← mapRows_rowFiniteEquiv_symm,
    ← mapRows_multiplication, rowFiniteEquiv_mapRows]
  rfl

/-- Scalar extension of the coefficient tensor is the actual multiplication over L. -/
theorem extend_coordinate : BilinearScalarExtension.extend (L := L) (coordinate (K := K) (m := m)) =
    coordinate (K := L) (m := m) := by
  classical
  apply (Pi.basisFun L (Fin (FormCount m 2))).ext
  intro f
  apply (Pi.basisFun L (Fin (RowCount m 1))).ext
  intro v
  funext k
  simp only [Pi.basisFun_apply,BilinearScalarExtension.extend_basis]
  have h := coordinate_map (L := L) (Pi.single f (1 : K)) (Pi.single v (1 : K)) k
  have hf : (fun i : Fin (FormCount m 2) => algebraMap K L
      ((Pi.single f (1 : K) : Fin (FormCount m 2) → K) i)) =
      (Pi.single f (1 : L) : Fin (FormCount m 2) → L) := by
    funext i
    simp [Pi.single_apply]
  have hv : (fun i : Fin (RowCount m 1) => algebraMap K L
      ((Pi.single v (1 : K) : Fin (RowCount m 1) → K) i)) =
      (Pi.single v (1 : L) : Fin (RowCount m 1) → L) := by
    funext i
    simp [Pi.single_apply]
  rw [hf,hv] at h
  exact h.symm

/-- Coordinate images are the actual images transported by the target equivalence. -/
theorem image_coordinate (S : Submodule K (Rows K m 1)) :
    BilinearImage.image coordinate (S.map rowFiniteEquiv.toLinearMap) =
      (BilinearImage.image multiplication S).map rowFiniteEquiv.toLinearMap := by
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
      BilinearImage.image coordinate (S.map rowFiniteEquiv.toLinearMap)
    simpa only [coordinate_apply,LinearEquiv.symm_apply_apply] using hp

theorem image_coordinate_finrank (S : Submodule K (Rows K m 1)) :
    finrank K (BilinearImage.image coordinate (S.map rowFiniteEquiv.toLinearMap)) =
      finrank K (BilinearImage.image multiplication S) := by
  rw [image_coordinate,LinearEquiv.finrank_map_eq]

end Quartic.RowMultiplicationCoordinates
