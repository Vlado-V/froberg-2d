module

public import Froberg.AttachedStrictModelOpen
public import Froberg.GeometricPrivateModel
public import Froberg.VectorParameters

@[expose] public section

/-! A geometric private-column witness produces an actual nonempty open in
all coefficients of the homogeneous vector generators. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PrivateColumns
open Module MvPolynomial OuterInjection AttachedMultiplication VectorMultiplicationCoordinates
open VectorExpansionOpen
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]
  {k a z s b h : ℕ}

theorem private_open_of_geometric_growth (hk : 0 < k) (hs : 2 ≤ s)
    (hh : h=k*(2*s+1).choose s) (hn : 0 < a+z)
    (hc : 0 < Fintype.card (Labels k a s ⊕ Fin b))
    (ι : Fin b ↪ Fin z) (u : Labels k a s ⊕ Fin b → Fin h → K)
    (hu : ∀ U : Finset (Labels k a s ⊕ Fin b),U.card ≤ h → LinearIndependent K (fun i : U => u i.val))
    (G : ℝ)
    (hA : 0 < finrank L (PrivateSourceSpace ι (fun i j => algebraMap K L (u i j))))
    (hGA : (finrank L (PrivateSourceSpace ι (fun i j => algebraMap K L (u i j))) : ℝ) ≤ G)
    (hbound : ∀ V : Submodule L (PrivateSourceSpace ι (fun i j => algebraMap K L (u i j))),
      ((finrank L (PrivateTargetSpace ι (fun i j => algebraMap K L (u i j))) : ℝ)/
        finrank L (PrivateSourceSpace ι (fun i j => algebraMap K L (u i j))))*finrank L V+
        G*(min (finrank L V)
          (finrank L (PrivateSourceSpace ι (fun i j => algebraMap K L (u i j)))-finrank L V) : ℕ) ≤
        (finrank L (outerImage (d := s+1) (attachedExponent ι)
          (fun i j => algebraMap K L (u i j)) (attachedExponent_degree ι) V) : ℝ)) :
    ∃ D : MvPolynomial (VectorParameters.Index h (a+z) s (Fintype.card (Labels k a s ⊕ Fin b))) K,
      (∃ p,eval p D ≠ 0) ∧ ∀ p,eval p D ≠ 0 →
        StrictModel (VectorParameters.generators p) (s+1) G := by
  classical
  let r := (Fintype.equivFin (Labels k a s ⊕ Fin b)).symm
  let p₀ := VectorParameters.coordinates (generator (attachedExponent ι) u (attachedExponent_degree ι) ∘ r)
  have huL := MixedExterior.full_spark_map_coordinates (algebraMap K L) u hu
  have hsmall := private_small_fiber_bound hk hs hh
  have hi c (hc : c ≤ s+1) := attached_multiplication_injective hs ι hh.ge hsmall u hu c hc
  have hiL c (hc : c ≤ s+1) := attached_multiplication_injective hs ι hh.ge hsmall
    (fun i j => algebraMap K L (u i j)) huL c hc
  obtain ⟨D,hD,hgood⟩ := principal_open_strict_model_from_attached (L := L) r hc
    (attachedExponent ι) u (attachedExponent_degree ι) hn VectorParameters.generators
    VectorParameters.generators_polynomial p₀ (VectorParameters.generators_coordinates _)
    (hi 0 (Nat.zero_le _)) (hi (s+1) le_rfl)
    (hiL 0 (Nat.zero_le _)) (hiL (s+1) le_rfl) G hA hGA hbound
  exact ⟨D,⟨p₀,hD⟩,hgood⟩

end Froberg.PrivateColumns
