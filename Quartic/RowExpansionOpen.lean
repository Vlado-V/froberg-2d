module

public import Quartic.RowMultiplicationCoordinates
public import Quartic.BilinearExpansionOpen

@[expose] public section

/-! # Actual row-polynomial expansion on an open family of mixed columns -/
noncomputable section
namespace Quartic.RowExpansionOpen
open Module MvPolynomial Matrix RowMultiplicationCoordinates
open HomogeneousCoefficientCoordinates
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {m c d e : ℕ} {I : Type*}

def columnMatrix (g : Fin c → Rows K m 1) : Matrix (Fin (RowCount m 1)) (Fin c) K :=
  fun i j => rowFiniteEquiv (g j) i

theorem columnMatrix_range (g : Fin c → Rows K m 1) :
    LinearMap.range (columnMatrix g).mulVecLin =
      (Submodule.span K (Set.range g)).map rowFiniteEquiv.toLinearMap := by
  rw [Matrix.range_mulVecLin,Submodule.map_span,← Set.range_comp]
  rfl

theorem columnMatrix_map (g : Fin c → Rows K m 1) :
    (columnMatrix g).map (algebraMap K L) = columnMatrix (fun j => mapRows (L := L) (g j)) := by
  ext i j
  exact (rowFiniteEquiv_mapRows (g j) i).symm

def Expands (g : Fin c → Rows K m 1) (d e : ℕ) : Prop :=
  ∀ S : Submodule K (Rows K m 1), Submodule.span K (Set.range g) ≤ S → finrank K S = d →
    e ≤ finrank K (BilinearImage.image multiplication S)

/-- The coordinate assertion is exactly the assertion on actual row polynomials. -/
theorem expands_iff_coordinate (g : Fin c → Rows K m 1) :
    Expands g d e ↔ BilinearExpansionOpen.ExpandsContaining (columnMatrix g) coordinate d e := by
  constructor
  · intro h T hT hE
    let S := T.map rowFiniteEquiv.symm.toLinearMap
    have hback : S.map rowFiniteEquiv.toLinearMap = T :=
      (Submodule.map_symm_eq_iff rowFiniteEquiv).mp rfl
    have hS : finrank K S = d := by
      change finrank K (T.map rowFiniteEquiv.symm.toLinearMap) = d
      rw [LinearEquiv.finrank_map_eq,hT]
    have hES : Submodule.span K (Set.range g) ≤ S := by
      apply (Submodule.map_le_map_iff_of_injective rowFiniteEquiv.injective _ _).mp
      rw [hback,← columnMatrix_range]
      exact hE
    have hb := h S hES hS
    rw [← image_coordinate_finrank S,hback] at hb
    exact hb
  · intro h S hES hS
    have hdim : finrank K (S.map rowFiniteEquiv.toLinearMap) = d := by
      rw [LinearEquiv.finrank_map_eq,hS]
    have hinc : LinearMap.range (columnMatrix g).mulVecLin ≤ S.map rowFiniteEquiv.toLinearMap := by
      rw [columnMatrix_range]
      exact Submodule.map_mono hES
    have hb := h (S.map rowFiniteEquiv.toLinearMap) hdim hinc
    rwa [image_coordinate_finrank] at hb

/-- An actual geometric row-multiplication witness produces an open family
of actual K-valued mixed columns satisfying the same all-subspaces bound. -/
theorem principal_open [NeZero d] [IsAlgClosed L]
    (g : (I → K) → Fin c → Rows K m 1)
    (hg : ∀ j, IsPolynomialFamily (fun p => g p j)) (p₀ : I → K)
    (hwitness : Expands (fun j => mapRows (L := L) (g p₀ j)) d e) :
    ∃ D : MvPolynomial I K, eval p₀ D ≠ 0 ∧ ∀ p : I → K, eval p D ≠ 0 → Expands (g p) d e := by
  have hE : ∀ i j, IsPolynomialFamily (fun p => columnMatrix (g p) i j) := by
    intro i j
    exact (hg j).linear_comp ((LinearMap.proj i).comp rowFiniteEquiv.toLinearMap)
  have hw : BilinearExpansionOpen.ExpandsContaining
      ((columnMatrix (g p₀)).map (algebraMap K L))
      (BilinearScalarExtension.extend (L := L) (coordinate (K := K) (m := m))) d e := by
    rw [columnMatrix_map,extend_coordinate]
    exact (expands_iff_coordinate _).mp hwitness
  obtain ⟨D,hD,hgood⟩ := BilinearExpansionOpen.principal_open_containing_base
    (fun p => columnMatrix (g p)) hE (fun _ : I → K => coordinate (K := K) (m := m))
    (fun f v k => isPolynomialFamily_const _) p₀ hw
  exact ⟨D,hD,fun p hp => (expands_iff_coordinate _).mpr (hgood p hp)⟩

/-- Actual convolution columns have coefficients 0 and 1 and commute with base extension. -/
theorem mapRows_convolution (t w : ℕ) (k : Fin (t+2)) :
    mapRows (L := L) (GenericF13Endpoint.convolutionMixed K t w k) =
      GenericF13Endpoint.convolutionMixed L t w k := by
  classical
  funext r
  apply Subtype.ext
  simp only [mapRows,mapForm,GenericF13Endpoint.convolutionMixed,Submodule.coe_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : ConvolutionPresentation.columnIndex r i = k <;> simp [h]

/-- Specialization at the concrete convolution columns, retaining actual
polynomial parameter families for all varying mixed columns. -/
theorem principal_open_convolution {t w d e : ℕ} [NeZero d] [IsAlgClosed L]
    (g : (I → K) → Fin (t+2) → Rows K (t+w) 1)
    (hg : ∀ j, IsPolynomialFamily (fun p => g p j)) (p₀ : I → K)
    (hp₀ : g p₀ = GenericF13Endpoint.convolutionMixed K t w)
    (hwitness : Expands (GenericF13Endpoint.convolutionMixed L t w) d e) :
    ∃ D : MvPolynomial I K, eval p₀ D ≠ 0 ∧ ∀ p : I → K, eval p D ≠ 0 → Expands (g p) d e := by
  apply principal_open (L := L) g hg p₀
  simpa only [hp₀,mapRows_convolution] using hwitness

end Quartic.RowExpansionOpen
