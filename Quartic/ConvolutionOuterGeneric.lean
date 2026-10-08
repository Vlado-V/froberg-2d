import Quartic.ConvolutionOuterIncidence
import Quartic.BilinearGeneric

/-!
# Generic injective outer multiplication at the convolution presentation

For every canonical endpoint with child dimension at least 41, the actual
image bounds produce a nonempty principal open of injective outer maps. The
quadratic generators on that open are independent, and the actual quotient
has the exact Euler dimension. The convolution presentation is fixed here;
no varying-presentation or (1,3) covector-locus conclusion is asserted.
-/
noncomputable section
namespace Quartic.ConvolutionOuterGeneric
open Module MvPolynomial ConvolutionFreePieces ConvolutionFreeMultiplication
open ConvolutionOuterIncidence ProfileCertificate UniformEndpoint PolynomialBilinearCoordinates
variable {K : Type*} [Field K] {t w q : ℕ}

/-- The complete actual quadratic coefficient space at a canonical endpoint. -/
abbrev EndpointCoefficients (K : Type*) [Field K] (m : ℕ) (upper : Bool) :=
  Coefficients K (coreP (mixedCount m upper) + 1) (freeW m (mixedCount m upper))
    (upperEndpoint m)

/-- The actual quotient after imposing the ordered quadratic generators on N₁. -/
abbrev OuterQuotient (Q : Coefficients K t w q) :=
  Piece K t w 3 ⧸ LinearMap.range (outerMap Q)

/-- The proven incidence criterion gives a nonempty coefficient open of
injective outer maps at every canonical endpoint with m≥41. -/
theorem generic_outer_injective [Infinite K] (m : ℕ) (hm : 41 ≤ m) (upper : Bool) :
    ∃ P : MvPolynomial (Fin (finrank K (EndpointCoefficients K m upper))) K,
      (∃ Q : EndpointCoefficients K m upper,
        eval (coordinates K (EndpointCoefficients K m upper) Q) P ≠ 0) ∧
      ∀ Q : EndpointCoefficients K m upper,
        eval (coordinates K (EndpointCoefficients K m upper) Q) P ≠ 0 →
          Function.Injective (outerMap Q) := by
  apply BilinearGeneric.generic_injective_actual bilinear.flip
  intro L _
  exact endpoint_actual_incidence_rank_bound m hm upper L

/-- In particular, an actual tuple of quadrics makes the outer map injective. -/
theorem exists_outer_injective [Infinite K] (m : ℕ) (hm : 41 ≤ m) (upper : Bool) :
    ∃ Q : EndpointCoefficients K m upper, Function.Injective (outerMap Q) := by
  obtain ⟨P, ⟨Q, hQ⟩, hgood⟩ := generic_outer_injective (K := K) m hm upper
  exact ⟨Q, hgood Q hQ⟩

/-- The first quotient piece is nonzero whenever the core has at least two variables. -/
theorem source_exists_ne_zero (ht : 2 ≤ t) : ∃ x : Piece K t w 1, x ≠ 0 := by
  have hdim : 0 < finrank K (Piece K t w 1) := by
    rw [(pieceSuccEquiv (K := K) (t := t) (w := w) (j := 0)).finrank_eq,
      ConvolutionFree.degreeOne_finrank ht]
    omega
  exact ⟨(Module.finBasis K (Piece K t w 1)) ⟨0, hdim⟩,
    (Module.finBasis K (Piece K t w 1)).ne_zero _⟩

/-- Injectivity of outer multiplication forces independence of the actual
quadrics, by multiplying a scalar relation by one nonzero class in N₁. -/
theorem independent_of_outer_injective (ht : 2 ≤ t) (Q : Coefficients K t w q)
    (hQ : Function.Injective (outerMap Q)) : LinearIndependent K Q := by
  obtain ⟨x, hx⟩ := source_exists_ne_zero (K := K) (w := w) ht
  apply Fintype.linearIndependent_iff.mpr
  intro s hs i
  have hz : outerMap Q (fun j => s j • x) = 0 := by
    have h := congrArg (fun f => ConvolutionInitialImage.pieceBilinear f x) hs
    rw [outerMap_apply]
    change (∑ j, ConvolutionInitialImage.pieceBilinear (Q j) (s j • x)) = 0
    simpa only [map_sum, LinearMap.sum_apply, map_smul,
      LinearMap.smul_apply, map_zero, LinearMap.zero_apply] using h
  have htup : (fun j => s j • x) = 0 := hQ (hz.trans (map_zero _).symm)
  exact (smul_eq_zero.mp (congrFun htup i)).resolve_right hx

/-- Rank-nullity gives the exact quotient dimension for every injective outer map. -/
theorem quotient_finrank (Q : Coefficients K t w q) (hQ : Function.Injective (outerMap Q)) :
    finrank K (OuterQuotient Q) = finrank K (Piece K t w 3) -
      q * finrank K (Piece K t w 1) := by
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.range (outerMap Q))
  rw [LinearMap.finrank_range_of_inj hQ] at h
  have hs : finrank K (SourceTuple K t w q) = q * finrank K (Piece K t w 1) := by
    calc
      _ = ∑ j : Fin q, finrank K (Piece K t w 1) := Module.finrank_pi_fintype K
      _ = _ := by simp
  rw [hs] at h
  change finrank K (OuterQuotient Q) + _ = _ at h
  omega

/-- The quotient dimension in the original free-extension Hilbert counts. -/
theorem quotient_finrank_hilbert (ht : 2 ≤ t) (Q : Coefficients K t w q)
    (hQ : Function.Injective (outerMap Q)) :
    finrank K (OuterQuotient Q) =
      t.choose 2 * w + 2 * (t - 1) * (w + 1).choose 2 + 3 * (w + 2).choose 3 -
        q * (2 * (t - 1) + 3 * w) := by
  rw [quotient_finrank Q hQ,
    (pieceSuccEquiv (K := K) (t := t) (w := w) (j := 2)).finrank_eq,
    (pieceSuccEquiv (K := K) (t := t) (w := w) (j := 0)).finrank_eq,
    ConvolutionFree.degreeThree_finrank ht, ConvolutionFree.degreeOne_finrank ht]

/-- All endpoint column counts lie in the range of the actual convolution model. -/
theorem endpoint_columns_range (m : ℕ) (hm : 41 ≤ m) (upper : Bool) :
    4 ≤ mixedCount m upper ∧ mixedCount m upper ≤ m := by
  by_cases hsmall : m ≤ 319
  · have h := (FiniteCounts.structural_binomial_counts m (by omega) hsmall upper)
    simp only [mixedCount_eq_table m hsmall]
    exact ⟨h.1, h.2.1⟩
  · exact UniformScalar.c_range m (by omega) upper

/-- The core and free variables together are exactly the ambient child variables. -/
theorem endpoint_variable_count (m : ℕ) (hm : 41 ≤ m) (upper : Bool) :
    coreP (mixedCount m upper) + 1 + freeW m (mixedCount m upper) = m := by
  have hc := endpoint_columns_range m hm upper
  unfold coreP freeW
  omega

/-- The actual cubic target has the source Euler count T, at every canonical endpoint. -/
theorem endpoint_target_euler (m : ℕ) (hm : 41 ≤ m) (upper : Bool) :
    (finrank K (Piece K (coreP (mixedCount m upper) + 1)
      (freeW m (mixedCount m upper)) 3) : ℤ) =
        UniformScalar.targetCount m (mixedCount m upper) := by
  have hc := endpoint_columns_range m hm upper
  have ht : 2 ≤ coreP (mixedCount m upper) + 1 := by unfold coreP; omega
  have hvars : coreP (mixedCount m upper) + 1 + freeW m (mixedCount m upper) = m := by
    unfold coreP freeW
    omega
  have hcols : coreP (mixedCount m upper) + 1 + 2 = mixedCount m upper := by
    unfold coreP
    omega
  have h := ConvolutionFree.degreeThree_euler (K := K)
    (w := freeW m (mixedCount m upper)) ht
  have hh : finrank K (ConvolutionFree.Cokernel K (coreP (mixedCount m upper) + 1)
      (freeW m (mixedCount m upper)) 2) +
      mixedCount m upper * (m + 1).choose 2 = 3 * (m + 2).choose 3 := by
    simpa only [hvars, hcols] using h
  have he : (finrank K (ConvolutionFree.Cokernel K (coreP (mixedCount m upper) + 1)
      (freeW m (mixedCount m upper)) 2) : ℤ) +
      (mixedCount m upper : ℤ) * ((m + 1).choose 2 : ℤ) = 3 * ((m + 2).choose 3 : ℤ) := by
    exact_mod_cast hh
  rw [(pieceSuccEquiv (K := K) (t := coreP (mixedCount m upper) + 1)
    (w := freeW m (mixedCount m upper)) (j := 2)).finrank_eq]
  unfold UniformScalar.targetCount Counts.b2 Counts.b3
  omega

/-- Every injective endpoint outer map has quotient dimension exactly j=T−qa. -/
theorem endpoint_quotient_finrank_eq_j (m : ℕ) (hm : 41 ≤ m) (upper : Bool)
    (Q : EndpointCoefficients K m upper) (hQ : Function.Injective (outerMap Q)) :
    (finrank K (OuterQuotient Q) : ℤ) =
      Counts.j m (upperEndpoint m) (mixedCount m upper) := by
  have hc := endpoint_columns_range m hm upper
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.range (outerMap Q))
  rw [LinearMap.finrank_range_of_inj hQ] at h
  have hs : finrank K (SourceTuple K (coreP (mixedCount m upper) + 1)
      (freeW m (mixedCount m upper)) (upperEndpoint m)) =
      upperEndpoint m * totalA m (mixedCount m upper) := by
    calc
      _ = ∑ j : Fin (upperEndpoint m), finrank K (Piece K (coreP (mixedCount m upper) + 1)
          (freeW m (mixedCount m upper)) 1) := Module.finrank_pi_fintype K
      _ = _ := by simp [endpoint_source_finrank m hm upper]
  rw [hs] at h
  have he : (finrank K (OuterQuotient Q) : ℤ) +
      (upperEndpoint m : ℤ) * (totalA m (mixedCount m upper) : ℤ) =
      (finrank K (Piece K (coreP (mixedCount m upper) + 1)
        (freeW m (mixedCount m upper)) 3) : ℤ) := by exact_mod_cast h
  rw [endpoint_target_euler m hm upper, totalA_eq m _ hc.1 hc.2,
    Nat.cast_sub (by omega : mixedCount m upper ≤ 3 * m)] at he
  push_cast at he
  unfold UniformScalar.targetCount Counts.j Counts.beta Counts.alpha at *
  nlinarith

/-- One nonempty principal open simultaneously gives independent actual
quadrics, injective outer multiplication, and the exact outer quotient count. -/
theorem generic_outer_exact [Infinite K] (m : ℕ) (hm : 41 ≤ m) (upper : Bool) :
    ∃ P : MvPolynomial (Fin (finrank K (EndpointCoefficients K m upper))) K,
      (∃ Q : EndpointCoefficients K m upper,
        eval (coordinates K (EndpointCoefficients K m upper) Q) P ≠ 0) ∧
      ∀ Q : EndpointCoefficients K m upper,
        eval (coordinates K (EndpointCoefficients K m upper) Q) P ≠ 0 →
          LinearIndependent K Q ∧ Function.Injective (outerMap Q) ∧
          (finrank K (OuterQuotient Q) : ℤ) =
            Counts.j m (upperEndpoint m) (mixedCount m upper) := by
  obtain ⟨P, hP, hgood⟩ := generic_outer_injective (K := K) m hm upper
  have hc := endpoint_columns_range m hm upper
  have ht : 2 ≤ coreP (mixedCount m upper) + 1 := by unfold coreP; omega
  refine ⟨P, hP, ?_⟩
  intro Q hQ
  have hi := hgood Q hQ
  exact ⟨independent_of_outer_injective ht Q hi, hi, endpoint_quotient_finrank_eq_j m hm upper Q hi⟩

/-- An actual independent quadratic tuple with injective outer multiplication
and the exact quotient count exists at every canonical endpoint. -/
theorem exists_outer_exact [Infinite K] (m : ℕ) (hm : 41 ≤ m) (upper : Bool) :
    ∃ Q : EndpointCoefficients K m upper,
      LinearIndependent K Q ∧ Function.Injective (outerMap Q) ∧
      (finrank K (OuterQuotient Q) : ℤ) =
        Counts.j m (upperEndpoint m) (mixedCount m upper) := by
  obtain ⟨P, ⟨Q, hQ⟩, hgood⟩ := generic_outer_exact (K := K) m hm upper
  exact ⟨Q, hgood Q hQ⟩

end Quartic.ConvolutionOuterGeneric
