import Quartic.BilinearContainingEquations

/-!
# Principal opens preserving all-subspaces bilinear expansion

Bad planes containing a varying presentation are encoded by an actual finite
homogeneous system. Geometric emptiness at a witness is proved equivalent to
the expansion bound; the Nullstellensatz then produces a principal open over
the original coefficient field. No positive-fiber dimension assertion occurs.
-/
noncomputable section
namespace Quartic.BilinearExpansionOpen
open Module Matrix MvPolynomial SubspaceMinorCoordinates SubspaceMinorContainment
open BilinearExpansionEquations BilinearImageMinors
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {a b t c d e : ℕ} {I : Type*}

/-- Every d-plane containing the actual presentation range has image dimension at least e. -/
def ExpandsContaining (E : Matrix (Fin a) (Fin c) K)
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K)) (d e : ℕ) : Prop :=
  ∀ S : Submodule K (Fin a → K), finrank K S = d →
    LinearMap.range E.mulVecLin ≤ S → e ≤ finrank K (BilinearImage.image mu S)

/-- Empty projective solution set is exactly the actual all-planes expansion assertion. -/
theorem empty_iff_expands [NeZero d] (E : Matrix (Fin a) (Fin c) K)
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K)) :
    (∀ q : Fin (ProjectiveCount a d) → L,
      (∀ x : BilinearContainingEquations.Index a b t c d e,
        aeval q (BilinearContainingEquations.equation E mu x).val = 0) → q = 0) ↔
      ExpandsContaining (E.map (algebraMap K L)) (BilinearScalarExtension.extend (L := L) mu) d e := by
  classical
  constructor
  · intro hempty S hS hE
    by_contra hbound
    have hbad : finrank L (BilinearImage.image (BilinearScalarExtension.extend (L := L) mu) S) < e :=
      Nat.lt_of_not_ge hbound
    obtain ⟨p,hp,hs,hcontains,hsub⟩ := cover_containing S hS (E.map (algebraMap K L)) hE
    let q : Fin (ProjectiveCount a d) → L := fun i => p ((rowIndex a d).symm i)
    have hdecode : decode q = p := by
      funext J
      simp [decode,q]
    have hzero : q = 0 := by
      apply hempty
      apply (BilinearContainingEquations.equations_iff E mu q).mpr
      rw [hdecode]
      refine ⟨hcontains,hs,?_⟩
      intro J
      have himage : BilinearImage.image (BilinearScalarExtension.extend (L := L) mu)
          (LinearMap.range (reconstruction p J).mulVecLin) ≤
          BilinearImage.image (BilinearScalarExtension.extend (L := L) mu) S :=
        iSup_mono (fun f => Submodule.map_mono (hsub J))
      rw [imageMatrix_rank, ← Matrix.range_mulVecLin]
      exact (Submodule.finrank_mono himage).trans_lt hbad
    apply hp
    rw [← hdecode]
    exact (decode_eq_zero_iff q).mpr hzero
  · intro hexpand q hq
    obtain ⟨hcontains,hs,hr⟩ := (BilinearContainingEquations.equations_iff E mu q).mp hq
    by_contra hzero
    have hnonzero : decode q ≠ 0 := fun h => hzero ((decode_eq_zero_iff q).mp h)
    obtain ⟨J,hJ⟩ := Function.ne_iff.mp hnonzero
    change decode q J ≠ 0 at hJ
    have hdim := reconstruction_finrank_of_selected hs J hJ
    have hinc := range_le_of_containsMatrix (E.map (algebraMap K L)) hcontains J hJ
    have hbound := hexpand (LinearMap.range (reconstruction (decode q) J).mulVecLin) hdim hinc
    have hsmall := hr J
    rw [imageMatrix_rank, ← Matrix.range_mulVecLin] at hsmall
    omega

/-- Geometric expansion implies the actual base-field assertion. This follows
from the equations by injectivity of the field embedding, with no assumed
matrix-rank descent lemma. -/
theorem expandsContaining_descends [NeZero d] (E : Matrix (Fin a) (Fin c) K)
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K))
    (h : ExpandsContaining (E.map (algebraMap K L))
      (BilinearScalarExtension.extend (L := L) mu) d e) : ExpandsContaining E mu d e := by
  have hb : ExpandsContaining (E.map (algebraMap K K))
      (BilinearScalarExtension.extend (L := K) mu) d e := by
    apply (empty_iff_expands (L := K) E mu).mp
    intro q hq
    have hz := (empty_iff_expands E mu).mpr h (fun i => algebraMap K L (q i)) (by
      intro x
      have he := MvPolynomial.comp_aeval_apply q (Algebra.ofId K L)
        (BilinearContainingEquations.equation E mu x).val
      exact he.symm.trans (by rw [hq x, map_zero]))
    funext i
    apply (algebraMap K L).injective
    simpa only [Pi.zero_apply, map_zero] using congrFun hz i
  have hE : E.map (algebraMap K K) = E := by ext; rfl
  simpa only [hE,BilinearScalarExtension.extend_self] using hb

/-- A geometrically valid witness spreads to a principal open over K, including
all d-planes over L containing the varying presentation. -/
theorem principal_open_containing [NeZero d] [IsAlgClosed L]
    (E : (I → K) → Matrix (Fin a) (Fin c) K)
    (hE : ∀ k j, IsPolynomialFamily (fun p => E p k j))
    (mu : (I → K) → (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K))
    (hmu : ∀ f v k, IsPolynomialFamily (fun p => mu p (Pi.single f 1) (Pi.single v 1) k))
    (p₀ : I → K)
    (hwitness : ExpandsContaining ((E p₀).map (algebraMap K L))
      (BilinearScalarExtension.extend (L := L) (mu p₀)) d e) :
    ∃ D : MvPolynomial I K, eval p₀ D ≠ 0 ∧ ∀ p : I → K, eval p D ≠ 0 →
      ExpandsContaining ((E p).map (algebraMap K L))
        (BilinearScalarExtension.extend (L := L) (mu p)) d e := by
  classical
  let J := BilinearContainingEquations.Index a b t c d e
  let ix := (Fintype.equivFin J).symm
  let deg : Fin (Fintype.card J) → ℕ := fun j => BilinearContainingEquations.degree (ix j)
  let fam : ∀ j : Fin (Fintype.card J), (I → K) → Forms K (ProjectiveCount a d) (deg j) :=
    fun j p => BilinearContainingEquations.equation (E p) (mu p) (ix j)
  have hpoly : ∀ j, IsPolynomialFamily (fam j) :=
    fun j => BilinearContainingEquations.equation_polynomial E hE mu hmu (ix j)
  have hempty : ∀ q : Fin (ProjectiveCount a d) → L,
      (∀ j, aeval q (fam j p₀).val = 0) → q = 0 := by
    intro q hq
    apply (empty_iff_expands (E p₀) (mu p₀)).mpr hwitness q
    intro x
    obtain ⟨j,rfl⟩ := ix.surjective x
    exact hq j
  obtain ⟨D,hD,hgood⟩ := HomogeneousEmptyFiberOpen.principal_open_empty_fiber deg fam hpoly p₀ hempty
  refine ⟨D,hD,?_⟩
  intro p hp
  apply (empty_iff_expands (E p) (mu p)).mp
  intro q hq
  exact hgood p hp q (fun j => hq (ix j))

/-- The same construction yields a principal open of actual expansion over K. -/
theorem principal_open_containing_base [NeZero d] [IsAlgClosed L]
    (E : (I → K) → Matrix (Fin a) (Fin c) K)
    (hE : ∀ k j, IsPolynomialFamily (fun p => E p k j))
    (mu : (I → K) → (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K))
    (hmu : ∀ f v k, IsPolynomialFamily (fun p => mu p (Pi.single f 1) (Pi.single v 1) k))
    (p₀ : I → K)
    (hwitness : ExpandsContaining ((E p₀).map (algebraMap K L))
      (BilinearScalarExtension.extend (L := L) (mu p₀)) d e) :
    ∃ D : MvPolynomial I K, eval p₀ D ≠ 0 ∧ ∀ p : I → K, eval p D ≠ 0 →
      ExpandsContaining (E p) (mu p) d e := by
  obtain ⟨D,hD,hgood⟩ := principal_open_containing E hE mu hmu p₀ hwitness
  exact ⟨D,hD,fun p hp => expandsContaining_descends (E p) (mu p) (hgood p hp)⟩

/-- The unrestricted expansion assertion, stated with actual submodules. -/
def Expands (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K)) (d e : ℕ) : Prop :=
  ∀ S : Submodule K (Fin a → K), finrank K S = d → e ≤ finrank K (BilinearImage.image mu S)

theorem expandsContaining_zero_iff
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K)) :
    ExpandsContaining (0 : Matrix (Fin a) (Fin 0) K) mu d e ↔ Expands mu d e := by
  constructor
  · intro h S hS
    exact h S hS (by simp)
  · intro h S hS _
    exact h S hS

/-- Without presentation constraints, every d-plane still satisfies the bound
throughout a principal open nonzero at the witness. -/
theorem principal_open [NeZero d] [IsAlgClosed L]
    (mu : (I → K) → (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K))
    (hmu : ∀ f v k, IsPolynomialFamily (fun p => mu p (Pi.single f 1) (Pi.single v 1) k))
    (p₀ : I → K)
    (hwitness : Expands (BilinearScalarExtension.extend (L := L) (mu p₀)) d e) :
    ∃ D : MvPolynomial I K, eval p₀ D ≠ 0 ∧ ∀ p : I → K, eval p D ≠ 0 →
      Expands (BilinearScalarExtension.extend (L := L) (mu p)) d e := by
  have hw : ExpandsContaining ((0 : Matrix (Fin a) (Fin 0) K).map (algebraMap K L))
      (BilinearScalarExtension.extend (L := L) (mu p₀)) d e := by
    simpa only [Matrix.map_zero _ (map_zero _)] using (expandsContaining_zero_iff _).mpr hwitness
  obtain ⟨D,hD,hgood⟩ := principal_open_containing (fun _ : I → K => (0 : Matrix (Fin a) (Fin 0) K))
    (fun k j => isPolynomialFamily_const _) mu hmu p₀ hw
  refine ⟨D,hD,?_⟩
  intro p hp
  apply (expandsContaining_zero_iff _).mp
  simpa only [Matrix.map_zero _ (map_zero _)] using hgood p hp

end Quartic.BilinearExpansionOpen
