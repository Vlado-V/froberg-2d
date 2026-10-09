module

public import Quartic.OrderedDegreeOne
public import Quartic.FilteredCoordinates
public import Quartic.ProfileChartBound
public import Quartic.ConvolutionProfileBound

@[expose] public section

/-!
# Actual convolution coordinates for the profile charts

The prefix order is exactly the order used by the checked multiplication-image
initial construction. Its constant slot is first; the other slots permute the
free variables. Thus polynomial profile charts and image certificates describe
the same actual subspace profile.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1500000

noncomputable section
namespace Quartic.ConvolutionProfileCoordinates
open Module FreeCoefficients ConvolutionFreePieces ConvolutionLayers
open ConvolutionInitialImage ConvolutionInitialSplit OrderedDegreeOne
open ProfileChartBound ConvolutionProfileRanks
variable {K : Type*} [Field K] {t w : ℕ}

/-- The order-preserving reindexing of the actual degree-one coefficient slots. -/
def orderCast (w : ℕ) : Fin (w+1) ≃o Fin (Fintype.card (BoundedExponent w 1)) where
  toEquiv := finCongr (card_bounded_one w).symm
  map_rel_iff' := Iff.rfl

abbrev DegreeBlock (K : Type*) [Field K] (t w : ℕ) (j : Fin (w+1)) :=
  CoreBlock K t w 1 (orderCast w j)

@[simp] theorem degreeBlock_zero :
    1-(enumeration w 0).val.degree=1 := by rw [enumeration_zero]; rfl
@[simp] theorem degreeBlock_succ (i : Fin w) :
    1-(enumeration w i.succ).val.degree=0 := by rw [enumeration_succ_degree]

theorem degreeBlock_finrank (ht : 2 ≤ t) (j : Fin (w+1)) :
    finrank K (DegreeBlock K t w j)=blockDimensions (2*(t-1)) w j := by
  change finrank K (Piece K t 0 (1-(enumeration w j).val.degree))=_
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [degreeBlock_zero,corePieceOne_finrank ht]
    rfl
  · rw [degreeBlock_succ,corePieceZero_finrank]
    rfl

/-- Coordinates inside each actual core block, with the manuscript block dimensions. -/
def blockCoordinates (ht : 2 ≤ t) (j : Fin (w+1)) :
    DegreeBlock K t w j ≃ₗ[K] (Fin (blockDimensions (2*(t-1)) w j) → K) :=
  (Module.finBasis K (DegreeBlock K t w j)).equivFun.trans
    (LinearEquiv.piCongrLeft' K (fun _ => K) (finCongr (degreeBlock_finrank (K := K) ht j)))

/-- Blockwise scalar coordinates on the already ordered quotient coefficients. -/
def coordinateChange (ht : 2 ≤ t) :
    ((i : Fin (Fintype.card (BoundedExponent w 1))) → CoreBlock K t w 1 i) ≃ₗ[K]
      IteratedBlockCharts.Ambient K (blockDimensions (2*(t-1)) w) :=
  (LinearEquiv.piCongrLeft' K _ (orderCast w).symm.toEquiv).trans
    (LinearEquiv.piCongrRight (blockCoordinates ht))

/-- Ordered scalar coordinates on the actual first convolution quotient piece. -/
def coordinates (ht : 2 ≤ t) : Piece K t w 1 ≃ₗ[K]
    IteratedBlockCharts.Ambient K (blockDimensions (2*(t-1)) w) :=
  orderedPiecesEquiv.trans (coordinateChange ht)

@[simp] theorem coordinates_apply (ht : 2 ≤ t) (x : Piece K t w 1) (j : Fin (w+1)) :
    coordinates ht x j=blockCoordinates ht j (orderedPiecesEquiv x (orderCast w j)) := rfl

set_option backward.isDefEq.respectTransparency true in
/-- The scalar-coordinate initial ranks are exactly the original quotient initial ranks. -/
theorem initial_finrank_coordinates (ht : 2 ≤ t) (S : Submodule K (Piece K t w 1))
    (j : Fin (w+1)) :
    finrank K (FilteredImage.initialPiece
      (fun i => Fin (blockDimensions (2*(t-1)) w i) → K)
      (S.map (coordinates ht).toLinearMap) j)=
      finrank K (initialCoefficients S (orderCast w j)) := by
  have heq : FilteredImage.initialPiece
      (fun i => Fin (blockDimensions (2*(t-1)) w i) → K)
      (S.map (coordinates ht).toLinearMap) j=
        (initialCoefficients S (orderCast w j)).map (blockCoordinates ht j).toLinearMap := by
    ext v
    rw [FilteredCoordinates.mem_initialPiece_iff]
    constructor
    · rintro ⟨x,⟨y,hy,rfl⟩,hzero,hv⟩
      refine ⟨orderedPiecesEquiv y (orderCast w j),?_,?_⟩
      · refine ⟨orderedPiecesEquiv y,⟨⟨y,hy,rfl⟩,?_⟩,rfl⟩
        intro k hk
        let l := (orderCast w).symm k
        have hlt : j<l := by
          apply (orderCast w).lt_iff_lt.mp
          change orderCast w j<(orderCast w) ((orderCast w).symm k)
          rw [OrderIso.apply_symm_apply]
          omega
        have hz := hzero l hlt
        change coordinates ht y l=0 at hz
        rw [coordinates_apply] at hz
        have hz' := (blockCoordinates ht l).injective
          (hz.trans (blockCoordinates ht l).map_zero.symm)
        have transport (a : Fin (Fintype.card (BoundedExponent w 1)))
            (h : a=k) (ha : orderedPiecesEquiv y a=0) : orderedPiecesEquiv y k=0 := by
          subst a
          exact ha
        exact transport _ ((orderCast w).apply_symm_apply k) hz'
      · change blockCoordinates ht j (orderedPiecesEquiv y (orderCast w j))=v
        exact hv
    · rintro ⟨v,⟨x,⟨⟨y,hy,hxy⟩,hflag⟩,hv⟩,rfl⟩
      change orderedPiecesEquiv y=x at hxy
      subst x
      change orderedPiecesEquiv y (orderCast w j)=v at hv
      subst v
      refine ⟨coordinates ht y,⟨y,hy,rfl⟩,?_,rfl⟩
      intro k hk
      rw [coordinates_apply,hflag (orderCast w k) (by
        have h := (orderCast w).strictMono hk
        omega),map_zero]
  exact (congrArg (fun T : Submodule K (Fin (blockDimensions (2*(t-1)) w j) → K) =>
    finrank K T) heq).trans ((blockCoordinates ht j).finrank_map_eq _)

/-- Projecting an independent product of coefficient subspaces recovers that component. -/
theorem map_pi_projection {n : ℕ} {E : Fin n → Type*}
    [∀ i,AddCommGroup (E i)] [∀ i,Module K (E i)]
    (C : ∀ i,Submodule K (E i)) (j : Fin n) :
    (Submodule.pi Set.univ C).map (LinearMap.proj j)=C j := by
  classical
  ext v
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact hx j (Set.mem_univ j)
  · intro hv
    refine ⟨Pi.single j v,?_,?_⟩
    · intro i _
      by_cases h : i=j
      · subst i
        simpa using hv
      · simp [Pi.single_eq_of_ne h]
    · simp

/-- The original initial coefficient is the projection of the actual initial subspace. -/
theorem coefficient_as_projection (S : Submodule K (Piece K t w 1))
    (j : Fin (Fintype.card (BoundedExponent w 1))) :
    (initial S).map ((LinearMap.proj j).comp orderedPiecesEquiv.toLinearMap)=
      initialCoefficients S j := by
  rw [Submodule.map_comp,map_initial]
  exact map_pi_projection (K := K) (E := CoreBlock K t w 1) (initialCoefficients S) j

/-- The first ordered coefficient is the actual core projection. -/
theorem cast_coefficient_core (x : Piece K t w 1) :
    pieceCast (degreeBlock_zero (w := w))
      (orderedPiecesEquiv x (orderCast w 0))=coreProjection x := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro v
  change pieceCast _ (orderedPiecesEquiv (Submodule.Quotient.mk v) (orderCast w 0))=
    (degreeOneEquiv (Submodule.Quotient.mk v)).1
  rw [orderedPiecesEquiv_apply,quotientPiecesEquiv_mk,pieceCast_mk,degreeOneEquiv_mk_core]
  apply congrArg (relations K t 0 1).mkQ
  funext r
  apply Subtype.ext
  simp only [targetCast_apply_val,targetPiecesEquiv_apply_val]
  change freeCoeff (enumeration w 0).val (v r).val=freeCoeff (zeroExponent w).val (v r).val
  rw [enumeration_zero]
  rfl

/-- Every later ordered coefficient is the actual projection at its permuted variable. -/
theorem cast_coefficient_free (x : Piece K t w 1) (i : Fin w) :
    pieceCast (degreeBlock_succ i)
      (orderedPiecesEquiv x (orderCast w i.succ))=freeProjection (freePermutation w i) x := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro v
  change pieceCast _ (orderedPiecesEquiv (Submodule.Quotient.mk v) (orderCast w i.succ))=
    (degreeOneEquiv (Submodule.Quotient.mk v)).2 (freePermutation w i)
  rw [orderedPiecesEquiv_apply,quotientPiecesEquiv_mk,pieceCast_mk,degreeOneEquiv_mk_free]
  apply congrArg (relations K t 0 0).mkQ
  funext r
  apply Subtype.ext
  simp only [targetCast_apply_val,targetPiecesEquiv_apply_val]
  change freeCoeff (enumeration w i.succ).val (v r).val=
    freeCoeff (oneExponentEquiv (freePermutation w i)).val (v r).val
  rw [enumeration_succ]
  rfl

/-- The first initial rank used by the charts is the core rank used by the image theorem. -/
theorem initial_core_finrank (S : Submodule K (Piece K t w 1)) :
    finrank K (initialCoefficients S (orderCast w 0))=finrank K (corePart (initial S)) := by
  let e : DegreeBlock K t w 0 ≃ₗ[K] Piece K t 0 1 := pieceCast degreeBlock_zero
  have he : (initialCoefficients S (orderCast w 0)).map e.toLinearMap=corePart (initial S) := by
    rw [←coefficient_as_projection,←Submodule.map_comp]
    apply congrArg (fun f => (initial S).map f)
    apply LinearMap.ext
    intro x
    exact cast_coefficient_core x
  exact (e.finrank_map_eq _).symm.trans (congrArg (fun T : Submodule K (Piece K t 0 1) => finrank K T) he)

/-- The later initial ranks are precisely the free ranks, in the certified permutation. -/
theorem initial_free_finrank (S : Submodule K (Piece K t w 1)) (i : Fin w) :
    finrank K (initialCoefficients S (orderCast w i.succ))=
      finrank K (freePart (initial S) (freePermutation w i)) := by
  let e : DegreeBlock K t w i.succ ≃ₗ[K] Piece K t 0 0 := pieceCast (degreeBlock_succ i)
  have he : (initialCoefficients S (orderCast w i.succ)).map e.toLinearMap=
      freePart (initial S) (freePermutation w i) := by
    rw [←coefficient_as_projection,←Submodule.map_comp]
    apply congrArg (fun f => (initial S).map f)
    apply LinearMap.ext
    intro x
    exact cast_coefficient_free x i
  exact (e.finrank_map_eq _).symm.trans (congrArg (fun T : Submodule K (Piece K t 0 0) => finrank K T) he)

/-- Actual ordered prefix ranks, in the scalar coordinates used by polynomial charts. -/
def ranks (ht : 2 ≤ t) (S : Submodule K (Piece K t w 1)) (j : Fin (w+1)) : ℕ :=
  finrank K (FilteredImage.initialPiece
    (fun i => Fin (blockDimensions (2*(t-1)) w i) → K)
    (S.map (coordinates ht).toLinearMap) j)

@[simp] theorem ranks_zero (ht : 2 ≤ t) (S : Submodule K (Piece K t w 1)) :
    ranks ht S 0=finrank K (corePart (initial S)) := by
  rw [ranks,initial_finrank_coordinates,initial_core_finrank]

@[simp] theorem ranks_succ (ht : 2 ≤ t) (S : Submodule K (Piece K t w 1)) (i : Fin w) :
    ranks ht S i.succ=finrank K (freePart (initial S) (freePermutation w i)) := by
  rw [ranks,initial_finrank_coordinates,initial_free_finrank]

/-- Permuting the free variables does not change any threshold count. -/
theorem levelCount_permutation (r : Fin w → ℕ) (e : Fin w ≃ Fin w) (h : ℕ) :
    LayerRankCounts.levelCount (fun i => r (e i)) h=LayerRankCounts.levelCount r h := by
  unfold LayerRankCounts.levelCount
  exact Fintype.card_congr (e.subtypeEquiv (by intro i; rfl))

end Quartic.ConvolutionProfileCoordinates
