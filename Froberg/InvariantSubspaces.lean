module

public import Froberg.SLCharacters
public import Froberg.PrimitivePlucker
public import Froberg.SemilinearMatrices

@[expose] public section

/-! # Central-weight divisibility for actual invariant subspaces

The determinant vector here is constructed from a basis of the subspace,
normalized over the polynomial coefficient ring, and proved fixed using
the absence of characters of special-linear groups.
-/

noncomputable section
namespace Froberg
open Matrix Module

variable {K I J : Type*} [Field K] [Infinite K]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- A line invariant under a product of two special-linear groups is fixed. -/
theorem sl_product_invariant_line_fixed {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (SpecialLinearGroup I K × SpecialLinearGroup J K) V)
    (v : V) (hv : v ≠ 0) (hline : ∀ g, ∃ a : K, ρ g v = a • v) :
    ∀ g, ρ g v = v := by
  have h₁ := sl_invariant_line_fixed (ρ.comp (MonoidHom.inl _ _)) v hv
    (fun g => hline (g, 1))
  have h₂ := sl_invariant_line_fixed (ρ.comp (MonoidHom.inr _ _)) v hv
    (fun g => hline (1, g))
  change ∀ g, ρ (g, 1) v = v at h₁
  change ∀ g, ρ (1, g) v = v at h₂
  intro g
  have hg : g = (g.1, 1) * (1, g.2) := by simp
  rw [hg, map_mul, Module.End.mul_apply, h₂, h₁]

variable {σ F : Type*} [Field F]
  [Algebra (MvPolynomial σ K) F] [IsFractionRing (MvPolynomial σ K) F]
  {n : ℕ}

/-- An actual invariant subspace has a fixed primitive determinant vector
over the original polynomial ring. -/
theorem invariant_subspace_exists_fixed_primitive_plucker
    (S : SemilinearMatrixAction K (MvPolynomial σ K)
      (SpecialLinearGroup I K × SpecialLinearGroup J K) (Fin n))
    (U : Submodule F (Fin n → F))
    (hU : ∀ g w, w ∈ U →
      (S.matrix g).map (algebraMap (MvPolynomial σ K) F) *ᵥ
        (fun i => IsFractionRing.ringEquivOfRingEquiv (S.coeff g).toRingEquiv (w i)) ∈ U) :
    ∃ v : Set.powersetCard (Fin n) (finrank F U) → MvPolynomial σ K,
      v ≠ 0 ∧ IsPrimitiveVector v ∧
        ∀ g, (S.exterior (finrank F U)).toRepresentation g v = v := by
  classical
  let b := Module.finBasis F U
  let p := pluckerCoordinates (fun i => (b i : Fin n → F))
  have hp0 : p ≠ 0 := basis_pluckerCoordinates_ne_zero U b
  obtain ⟨c, hc, v, hprim, hp⟩ :=
    exists_primitive_fraction_family (R := MvPolynomial σ K) p hp0
  have hv : v ≠ 0 := by
    intro h
    apply hp0
    funext i
    rw [hp i, h]
    simp
  refine ⟨v, hv, hprim, ?_⟩
  apply sl_product_invariant_line_fixed (S.exterior (finrank F U)).toRepresentation v hv
  intro g
  obtain ⟨a, ha⟩ := normalized_plucker_line_invariant U b (S.coeff g).toRingEquiv
    (S.matrix g) v c hc hp (hU g)
  have hprim' := (S.exterior (finrank F U)).primitive_toRepresentation hprim g
  obtain ⟨z, _, _, hz⟩ := primitive_polynomial_vectors_constant_scalar
    v ((S.exterior (finrank F U)).toRepresentation g v) hprim hprim' a ha
  refine ⟨z, ?_⟩
  funext i
  simpa only [Pi.smul_apply, MvPolynomial.smul_eq_C_mul] using hz i

/-- A central element fixing coefficient parameters and acting by weight
`e` forces the expected divisor of the actual subspace dimension. -/
theorem invariant_subspace_weight_divisibility
    (S : SemilinearMatrixAction K (MvPolynomial σ K)
      (SpecialLinearGroup I K × SpecialLinearGroup J K) (Fin n))
    (U : Submodule F (Fin n → F))
    (hU : ∀ g w, w ∈ U →
      (S.matrix g).map (algebraMap (MvPolynomial σ K) F) *ᵥ
        (fun i => IsFractionRing.ringEquivOfRingEquiv (S.coeff g).toRingEquiv (w i)) ∈ U)
    (z : SpecialLinearGroup I K × SpecialLinearGroup J K)
    (hcoeff : S.coeff z = 1) {l e : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ l)
    (hmat : (S.matrix z).map (algebraMap (MvPolynomial σ K) F) =
      ζ ^ e • (1 : Matrix (Fin n) (Fin n) F)) :
    l ∣ e * finrank F U := by
  classical
  obtain ⟨v, hv, _, hfix⟩ := invariant_subspace_exists_fixed_primitive_plucker S U hU
  let vf := fun i => algebraMap (MvPolynomial σ K) F (v i)
  have hvf : vf ≠ 0 := by
    intro h
    apply hv
    funext i
    apply IsFractionRing.injective (MvPolynomial σ K) F
    simpa only [vf, Pi.zero_apply, map_zero] using congrFun h i
  have hfixz : exteriorMatrix (finrank F U) (S.matrix z) *ᵥ v = v := by
    have hh := hfix z
    simpa only [SemilinearMatrixAction.toRepresentation_apply,
      SemilinearMatrixAction.exterior, hcoeff, AlgEquiv.one_apply] using hh
  have hf : (exteriorMatrix (finrank F U) (S.matrix z)).map
      (algebraMap (MvPolynomial σ K) F) *ᵥ vf = vf := by
    funext i
    exact ((algebraMap (MvPolynomial σ K) F).map_mulVec
      (exteriorMatrix (finrank F U) (S.matrix z)) v i).symm.trans
        (congrArg (algebraMap (MvPolynomial σ K) F) (congrFun hfixz i))
  rw [← exteriorMatrix_map, hmat] at hf
  exact exteriorMatrix_fixed_scalar_divisibility hζ vf hvf hf

end Froberg
