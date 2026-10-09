module

public import Quartic.SplitBlock22Homology

@[expose] public section

/-!
# The mixed–mixed quotient of actual (2,2) cycles

After the pure–child elimination, the remaining incoming maps are the
explicit constant Koszul relations on pairs of mixed generators. The
canonical mixed-coefficient projection identifies the two homology spaces.
-/
noncomputable section
namespace Quartic.SplitBlock22
open Module
open scoped TensorProduct
set_option maxHeartbeats 2000000
variable {K : Type*} [Field K] {m c q : ℕ}

/-- Commutativity of the actual polynomial product, before elimination. -/
theorem mixedProduct_comm (g a : MiddleCoordinates.Mixed K m) :
    mixedProduct g a = mixedProduct a g := by
  apply targetEmbedding_injective
  apply Subtype.ext
  rw [mixedProduct_polynomial, mixedProduct_polynomial, mul_comm]

/-- A coefficient supported at one mixed generator contributes its actual product. -/
theorem mixedMap_single (g : Fin c → MiddleCoordinates.Mixed K m)
    (i : Fin c) (a : MiddleCoordinates.Mixed K m) :
    mixedMap g (Pi.single i a) = mixedProduct (g i) a := by
  classical
  simp only [mixedMap, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Pi.single_apply]
  have he (j : Fin c) : mixedProduct (g j) (if j = i then a else 0) =
      if j = i then mixedProduct (g i) a else 0 := by split_ifs with h <;> simp_all
  simp_rw [he]
  simp

/-- The actual commutativity relation on every pair of mixed generators is a cycle. -/
theorem mixedMap_koszul (g : Fin c → MiddleCoordinates.Mixed K m) (p : GeneratorPair c) :
    mixedMap g (koszulVector g p) = 0 := by
  classical
  have he : koszulVector g p = Pi.single p.val.1 (g p.val.2) - Pi.single p.val.2 (g p.val.1) := by
    funext i
    simp only [koszulVector, Pi.sub_apply, Pi.single_apply]
  rw [he, map_sub, mixedMap_single, mixedMap_single, mixedProduct_comm, sub_self]

/-- Remaining incoming mixed–mixed boundaries, in their actual coefficient space. -/
def mixedKoszulSpace (g : Fin c → MiddleCoordinates.Mixed K m) :
    Submodule K (Fin c → MiddleCoordinates.Mixed K m) :=
  Submodule.span K (Set.range (koszulVector g))

theorem mixedKoszulSpace_le_kernel (g : Fin c → MiddleCoordinates.Mixed K m) :
    mixedKoszulSpace g ≤ (mixedMap g).ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p,rfl⟩
  exact mixedMap_koszul g p

theorem mixedKoszulSpace_le_quotient_kernel (g : Fin c → MiddleCoordinates.Mixed K m)
    (Q : Submodule K (Forms K m 2)) :
    mixedKoszulSpace g ≤ (MiddleCoordinates.quotientMap g Q).ker := by
  intro a ha
  change MiddleCoordinates.quotientMap g Q a = 0
  rw [← elimination_mixedMap, show mixedMap g a = 0 from mixedKoszulSpace_le_kernel g ha, map_zero]

/-- Insert mixed coefficients and zero pure and child coefficients. -/
def mixedSourceEmbedding : (Fin c → MiddleCoordinates.Mixed K m) →ₗ[K] Source K m c q :=
  (0 : (Fin c → MiddleCoordinates.Mixed K m) →ₗ[K] (Fin 4 → Forms K m 2)).prod
    (LinearMap.id.prod (0 : (Fin c → MiddleCoordinates.Mixed K m) →ₗ[K] (Fin q → Forms K 3 2)))

@[simp] theorem mixedSourceEmbedding_apply (a : Fin c → MiddleCoordinates.Mixed K m) :
    mixedSourceEmbedding (q := q) a = (0,a,0) := rfl

/-- Actual multiplication of these coefficient arrays. -/
@[simp] theorem multiplication_mixedSourceEmbedding (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (a : Fin c → MiddleCoordinates.Mixed K m) :
    multiplication g h (mixedSourceEmbedding a) = mixedMap g a := by
  change pureMap 0 + (mixedMap g a + childMap h 0) = mixedMap g a
  simp

/-- Both types of incoming boundaries in bidegree (2,2). -/
def blockBoundarySpace (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2) :
    Submodule K (Source K m c q) :=
  crossSpace h ⊔ (mixedKoszulSpace g).map mixedSourceEmbedding

theorem blockBoundarySpace_le_kernel (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) : blockBoundarySpace g h ≤ (multiplication g h).ker := by
  apply sup_le (crossSpace_le_kernel g h)
  rintro _ ⟨a,ha,rfl⟩
  change multiplication g h (mixedSourceEmbedding a) = 0
  rw [multiplication_mixedSourceEmbedding]
  exact mixedKoszulSpace_le_kernel g ha

/-- An actual block cycle is a boundary exactly when its mixed coefficient is a remaining boundary. -/
theorem boundary_iff_mixed_mem (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (hh : LinearIndependent K h)
    (a : (multiplication g h).ker) :
    a.val ∈ blockBoundarySpace g h ↔ a.val.2.1 ∈ mixedKoszulSpace g := by
  constructor
  · intro ha
    obtain ⟨u,hu,v,⟨b,hb,rfl⟩,he⟩ := Submodule.mem_sup.mp ha
    obtain ⟨t,rfl⟩ := hu
    have he' := congrArg (fun z : Source K m c q => z.2.1) he
    have hb' : b = a.val.2.1 := by simpa only [mixedSourceEmbedding_apply, crossBoundary,
      LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_add, Prod.snd_add, zero_add] using he'
    exact hb' ▸ hb
  · intro ha
    have hcycle : multiplication g h (a.val - mixedSourceEmbedding a.val.2.1) = 0 := by
      rw [map_sub, show multiplication g h a.val = 0 from a.property,
        multiplication_mixedSourceEmbedding,
        show mixedMap g a.val.2.1 = 0 from mixedKoszulSpace_le_kernel g ha, sub_self]
    have hz : (a.val - mixedSourceEmbedding (q := q) a.val.2.1).2.1 = 0 := by
      simp
    have hc := (cycle_zero_mixed_iff g h hh _ hcycle).mp hz
    apply Submodule.mem_sup.mpr
    refine ⟨a.val - mixedSourceEmbedding a.val.2.1, hc,
      mixedSourceEmbedding a.val.2.1, ⟨a.val.2.1,ha,rfl⟩, ?_⟩
    exact sub_add_cancel _ _

/-- Pulling the remaining boundaries back along the canonical projection gives exactly all block boundaries. -/
theorem blockBoundary_comap (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (hh : LinearIndependent K h) :
    kernelBoundary (W := Target K m) (multiplication g h) (blockBoundarySpace g h) =
      (kernelBoundary (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)))
        (mixedKoszulSpace g)).comap (cycleProjection g h) := by
  ext a
  change a.val ∈ blockBoundarySpace g h ↔ (cycleProjection g h a).val ∈ mixedKoszulSpace g
  exact boundary_iff_mixed_mem g h hh a

def quotientTransport {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) (A : Submodule K V) (B : Submodule K W)
    (hA : A = B.comap f) (hs : Function.Surjective f) : (V ⧸ A) ≃ₗ[K] (W ⧸ B) :=
  (Submodule.quotEquivOfEq _ _ (by rw [LinearMap.ker_comp, Submodule.ker_mkQ]; exact hA)).trans
    ((B.mkQ.comp f).quotKerEquivOfSurjective (B.mkQ_surjective.comp hs))

/-- The full incoming-boundary quotient of actual block cycles. -/
abbrev BlockHomology (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2) :=
  KernelModulo (W := Target K m) (multiplication g h) (blockBoundarySpace g h)

/-- The middle quotient-map kernel modulo the actual pairwise mixed relations. -/
abbrev MiddleHomology (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2) :=
  KernelModulo (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))) (mixedKoszulSpace g)

/-- Canonical homology identification induced by the actual mixed coefficient projection. -/
def homologyEquiv (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (hh : LinearIndependent K h) :
    BlockHomology g h ≃ₗ[K] MiddleHomology g h :=
  quotientTransport (K := K) (V := (multiplication g h).ker)
    (W := (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))).ker)
    (cycleProjection g h) _ _ (blockBoundary_comap g h hh)
    (cycleProjection_surjective g h)

@[simp] theorem homologyEquiv_mk (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (hh : LinearIndependent K h) (a : (multiplication g h).ker) :
    homologyEquiv g h hh (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (cycleProjection g h a) := by
  simp [homologyEquiv, quotientTransport]

/-- The remaining incoming relations have the expected independent pair count. -/
theorem mixedIncoming_finrank (g : Fin c → MiddleCoordinates.Mixed K m)
    (hg : LinearIndependent K g) (Q : Submodule K (Forms K m 2)) :
    finrank K (kernelBoundary (MiddleCoordinates.quotientMap g Q) (mixedKoszulSpace g)) =
      c.choose 2 := by
  rw [kernelBoundary, (Submodule.comapSubtypeEquivOfLe
    (mixedKoszulSpace_le_quotient_kernel g Q)).finrank_eq]
  exact (finrank_span_eq_card (koszulVector_linearIndependent g hg)).trans card_generatorPair

/-- The source's middle homology count, derived from the canonical actual quotient equivalence. -/
theorem homology_finrank_balance (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (hg : LinearIndependent K g) (hh : LinearIndependent K h)
    (hs : Function.Surjective
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)))) :
    finrank K (BlockHomology g h) + c.choose 2 + 2 * ((m+1).choose 2 - q) = 3*m*c := by
  let Q := Submodule.span K (Set.range h)
  let F := MiddleCoordinates.quotientMap g Q
  have hhom := finrank_kernelModulo_add F (mixedKoszulSpace g)
  rw [mixedIncoming_finrank g hg Q] at hhom
  have hrank := F.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top] at hrank
  have hsource : finrank K (Fin c → MiddleCoordinates.Mixed K m) = 3*m*c := by
    simp [MiddleCoordinates.Mixed, Module.finrank_pi_fintype, finrank_forms]
    ring
  have hquot : finrank K (Forms K m 2 ⧸ Q) = (m+1).choose 2-q := by
    rw [Submodule.finrank_quotient, finrank_quadrics]
    simp only [Q, finrank_span_eq_card hh, Fintype.card_fin]
  have htarget : finrank K ((Forms K m 2 ⧸ Q) × (Forms K m 2 ⧸ Q)) =
      2*((m+1).choose 2-q) := by rw [Module.finrank_prod, hquot]; omega
  rw [hsource, htarget] at hrank
  rw [(homologyEquiv g h hh).finrank_eq]
  change finrank K (KernelModulo F (mixedKoszulSpace g)) + c.choose 2 +
    2*((m+1).choose 2-q) = 3*m*c
  omega

/-- The integer count `Counts.H` equals the actual block homology dimension. -/
theorem homology_finrank_eq_H (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (hg : LinearIndependent K g) (hh : LinearIndependent K h)
    (hs : Function.Surjective
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)))) :
    (finrank K (BlockHomology g h) : ℤ) = Counts.H m q c := by
  have hq : q ≤ (m+1).choose 2 := by
    have ht := (Submodule.span K (Set.range h)).finrank_quotient_add_finrank
    rw [finrank_span_eq_card hh, Fintype.card_fin, finrank_quadrics] at ht
    omega
  have hi := congrArg (fun n : ℕ => (n : ℤ)) (homology_finrank_balance g h hg hh hs)
  push_cast [Nat.cast_sub hq] at hi
  unfold Counts.H Counts.alpha Counts.b2
  linarith

end Quartic.SplitBlock22
