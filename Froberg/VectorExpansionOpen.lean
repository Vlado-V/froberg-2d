module

public import Froberg.VectorMultiplicationCoordinates
public import Quartic.BilinearExpansionOpen

@[expose] public section

/-! # Actual row-polynomial expansion on an open family of mixed columns -/
noncomputable section
namespace Froberg.VectorExpansionOpen
open Module MvPolynomial Matrix VectorMultiplicationCoordinates
open Quartic
open HomogeneousCoefficientCoordinates
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {h m c s t d e : ℕ} {I : Type*}

def columnMatrix (g : Fin c → Rows K h m s) : Matrix (Fin (RowCount h m s)) (Fin c) K :=
  fun i j => rowFiniteEquiv (g j) i

theorem columnMatrix_range (g : Fin c → Rows K h m s) :
    LinearMap.range (columnMatrix g).mulVecLin =
      (Submodule.span K (Set.range g)).map rowFiniteEquiv.toLinearMap := by
  rw [Matrix.range_mulVecLin,Submodule.map_span,← Set.range_comp]
  rfl

theorem columnMatrix_map (g : Fin c → Rows K h m s) :
    (columnMatrix g).map (algebraMap K L) = columnMatrix (fun j => mapRows (L := L) (g j)) := by
  ext i j
  exact (rowFiniteEquiv_mapRows (g j) i).symm

def Expands (g : Fin c → Rows K h m s) (t d e : ℕ) : Prop :=
  ∀ S : Submodule K (Rows K h m s), Submodule.span K (Set.range g) ≤ S → finrank K S = d →
    e ≤ finrank K (BilinearImage.image (multiplication (d := t)) S)

/-- The coordinate assertion is exactly the assertion on actual row polynomials. -/
theorem expands_iff_coordinate (g : Fin c → Rows K h m s) :
    Expands g t d e ↔ BilinearExpansionOpen.ExpandsContaining (columnMatrix g) (coordinate (d := t)) d e := by
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
    (g : (I → K) → Fin c → Rows K h m s)
    (hg : ∀ j, IsPolynomialFamily (fun p => g p j)) (p₀ : I → K)
    (hwitness : Expands (fun j => mapRows (L := L) (g p₀ j)) t d e) :
    ∃ D : MvPolynomial I K, eval p₀ D ≠ 0 ∧ ∀ p : I → K, eval p D ≠ 0 → Expands (g p) t d e := by
  have hE : ∀ i j, IsPolynomialFamily (fun p => columnMatrix (g p) i j) := by
    intro i j
    exact (hg j).linear_comp ((LinearMap.proj i).comp rowFiniteEquiv.toLinearMap)
  have hw : BilinearExpansionOpen.ExpandsContaining
      ((columnMatrix (g p₀)).map (algebraMap K L))
      (BilinearScalarExtension.extend (L := L) (coordinate (d := t) (K := K) (h := h) (m := m) (s := s))) d e := by
    rw [columnMatrix_map,extend_coordinate]
    exact (expands_iff_coordinate _).mp hwitness
  obtain ⟨D,hD,hgood⟩ := BilinearExpansionOpen.principal_open_containing_base
    (fun p => columnMatrix (g p)) hE (fun _ : I → K => coordinate (d := t) (K := K) (m := m))
    (fun f v k => isPolynomialFamily_const _) p₀ hw
  exact ⟨D,hD,fun p hp => (expands_iff_coordinate _).mpr (hgood p hp)⟩

/-- A single principal open preserves every member of a finite list of
all-plane expansion bounds, retaining the given geometric witness. -/
theorem principal_open_finite {A : Type*} [Fintype A] [IsAlgClosed L]
    (g : (I → K) → Fin c → Rows K h m s)
    (hg : ∀ j, IsPolynomialFamily (fun p => g p j)) (p₀ : I → K)
    (degree imageBound : A → ℕ) (hdegree : ∀ i,0 < degree i)
    (hwitness : ∀ i,Expands (fun j => mapRows (L := L) (g p₀ j)) t (degree i) (imageBound i)) :
    ∃ D : MvPolynomial I K,eval p₀ D ≠ 0 ∧ ∀ p : I → K,eval p D ≠ 0 →
      ∀ i,Expands (g p) t (degree i) (imageBound i) := by
  classical
  have hex (i : A) : ∃ D : MvPolynomial I K,eval p₀ D ≠ 0 ∧
      ∀ p : I → K,eval p D ≠ 0 → Expands (g p) t (degree i) (imageBound i) := by
    letI : NeZero (degree i) := ⟨(hdegree i).ne'⟩
    exact principal_open g hg p₀ (hwitness i)
  choose D hD hgood using hex
  refine ⟨∏ i,D i,?_,?_⟩
  · simpa only [map_prod] using Finset.prod_ne_zero_iff.mpr (fun i _ => hD i)
  · intro p hp i
    have hp' : ∀ i ∈ Finset.univ,eval p (D i) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mp
      simpa only [map_prod] using hp
    exact hgood i p (hp' i (Finset.mem_univ i))

end Froberg.VectorExpansionOpen
