module

public import Quartic.RowExpansionOpen
public import Quartic.ConvolutionAmbientBounds

@[expose] public section

/-!
# Simultaneous expansion for varying actual mixed columns

For every canonical endpoint with m at least 41, a single principal open
preserves convolution's attained expansion thresholds in every source
dimension. The thresholds retain both scalar incidence bounds. The ambient
polynomial multiplication is fixed; all mixed presentation columns vary.
-/
noncomputable section
namespace Quartic.ConvolutionExpansionOpen
open Module MvPolynomial UniformEndpoint ProfileCertificate
open RowMultiplicationCoordinates RowExpansionOpen
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]
variable {I : Type*}

abbrev Dimensions (m : ℕ) (upper : Bool) := Fin (totalA m (mixedCount m upper)+1)

/-- Every monomial coefficient of every actual mixed column is a parameter. -/
abbrev ParameterIndex (m c : ℕ) := Fin c × RowIndex m 1

def decodeColumn {m c : ℕ} (j : Fin c) : (ParameterIndex m c → K) →ₗ[K] Rows K m 1 where
  toFun p := rowEquiv.symm (fun i => p (j,i))
  map_add' _ _ := rowEquiv.symm.map_add _ _
  map_smul' s _ := rowEquiv.symm.map_smul s _

def decode {m c : ℕ} (p : ParameterIndex m c → K) : Fin c → Rows K m 1 := fun j => decodeColumn j p

def encode {m c : ℕ} (g : Fin c → Rows K m 1) : ParameterIndex m c → K :=
  fun i => rowEquiv (g i.1) i.2

@[simp] theorem decode_encode {m c : ℕ} (g : Fin c → Rows K m 1) : decode (encode g) = g := by
  funext j
  exact rowEquiv.symm_apply_apply (g j)

@[simp] theorem encode_decode {m c : ℕ} (p : ParameterIndex m c → K) : encode (decode p) = p := by
  funext i
  exact congrFun (rowEquiv.apply_symm_apply (fun x => p (i.1,x))) i.2

/-- All numeric properties of the actual attained image thresholds. -/
def Thresholds (m : ℕ) (upper : Bool) (E : Dimensions m upper → ℕ) : Prop :=
  ∀ d : Dimensions m upper,
    (d.val : ℝ) * ((upperEndpoint m : ℝ) + (totalA m (mixedCount m upper) : ℝ) - d.val) ≤ E d ∧
    (0 < d.val → d.val < totalA m (mixedCount m upper) →
      SharpMinimization.ImageBoundsReal
        (HullCertificate.scalars m (upperEndpoint m) (mixedCount m upper)) (E d : ℝ) d.val)

include L

/-- One determinant open works for all source dimensions and all actual
ambient subspaces containing the varying mixed presentation. -/
theorem principal_open_family (m : ℕ) (hm : 41 ≤ m) (upper : Bool)
    (g : (I → K) → Fin ((coreP (mixedCount m upper)+1)+2) →
      Rows K ((coreP (mixedCount m upper)+1)+freeW m (mixedCount m upper)) 1)
    (hg : ∀ j, IsPolynomialFamily (fun p => g p j)) (p₀ : I → K)
    (hp₀ : g p₀ = GenericF13Endpoint.convolutionMixed K
      (coreP (mixedCount m upper)+1) (freeW m (mixedCount m upper))) :
    ∃ E : Dimensions m upper → ℕ, Thresholds m upper E ∧
      ∃ D : MvPolynomial I K, eval p₀ D ≠ 0 ∧ ∀ p : I → K, eval p D ≠ 0 →
        ∀ d : Dimensions m upper, RowExpansionOpen.Expands (g p)
          (d.val+mixedCount m upper) (E d+mixedCount m upper*(m+1).choose 2) := by
  classical
  have hthreshold : ∀ d : Dimensions m upper, ∃ e : ℕ,
      (d.val : ℝ) * ((upperEndpoint m : ℝ) + (totalA m (mixedCount m upper) : ℝ) - d.val) ≤ e ∧
      (0 < d.val → d.val < totalA m (mixedCount m upper) →
        SharpMinimization.ImageBoundsReal
          (HullCertificate.scalars m (upperEndpoint m) (mixedCount m upper)) (e : ℝ) d.val) ∧
      RowExpansionOpen.Expands (GenericF13Endpoint.convolutionMixed L
        (coreP (mixedCount m upper)+1) (freeW m (mixedCount m upper)))
        (d.val+mixedCount m upper) (e+mixedCount m upper*(m+1).choose 2) := by
    intro d
    obtain ⟨e,ho,hs,hb⟩ := ConvolutionAmbientBounds.exists_threshold (K := L) m hm upper d.val (by omega)
    exact ⟨e,ho,hs,hb⟩
  choose E houter hscalar hbound using hthreshold
  have hopen : ∀ d : Dimensions m upper, ∃ D : MvPolynomial I K,
      eval p₀ D ≠ 0 ∧ ∀ p : I → K, eval p D ≠ 0 →
        RowExpansionOpen.Expands (g p) (d.val+mixedCount m upper)
          (E d+mixedCount m upper*(m+1).choose 2) := by
    intro d
    have hc := ConvolutionOuterGeneric.endpoint_columns_range m hm upper
    let : NeZero (d.val+mixedCount m upper) := ⟨by omega⟩
    exact RowExpansionOpen.principal_open_convolution (L := L) g hg p₀ hp₀ (hbound d)
  choose D hD hgood using hopen
  refine ⟨E,fun d => ⟨houter d,hscalar d⟩,∏ d, D d,?_,?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun d _ => hD d)
  · intro p hp d
    have hn : eval p (D d) ≠ 0 :=
      Finset.prod_ne_zero_iff.mp (by simpa only [map_prod] using hp) d (Finset.mem_univ d)
    exact hgood d p hn

/-- The full actual mixed-coefficient family has a nonempty simultaneous
expansion open, with the concrete convolution point certifying nonemptiness. -/
theorem principal_open (m : ℕ) (hm : 41 ≤ m) (upper : Bool) :
    ∃ E : Dimensions m upper → ℕ, Thresholds m upper E ∧
      ∃ D : MvPolynomial
        (ParameterIndex ((coreP (mixedCount m upper)+1)+freeW m (mixedCount m upper))
          ((coreP (mixedCount m upper)+1)+2)) K,
        eval (encode (GenericF13Endpoint.convolutionMixed K
          (coreP (mixedCount m upper)+1) (freeW m (mixedCount m upper)))) D ≠ 0 ∧
        ∀ p, eval p D ≠ 0 → ∀ d : Dimensions m upper,
          RowExpansionOpen.Expands (decode p) (d.val+mixedCount m upper)
            (E d+mixedCount m upper*(m+1).choose 2) := by
  classical
  exact principal_open_family (L := L) m hm upper decode
    (fun j => isPolynomialFamily_linear (decodeColumn j))
    (encode (GenericF13Endpoint.convolutionMixed K
      (coreP (mixedCount m upper)+1) (freeW m (mixedCount m upper))))
    (decode_encode _)

end Quartic.ConvolutionExpansionOpen
