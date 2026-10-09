module

public import Quartic.Multiplication
public import Quartic.Counts

@[expose] public section

/-!
# Degree-four first Koszul homology

The incoming relation space is the span of the actual pairwise relations.
It lies in the actual multiplication kernel by commutativity. Quotienting this
kernel defines first Koszul homology in this degree, in ordered coordinates.
-/

noncomputable section

namespace Quartic

open Module

section GeneralKernelQuotient

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Pull a boundary space back to the kernel; the abstract construction fixes
the additive group instance before specializing to nested polynomial subspaces. -/
def kernelBoundary (f : V →ₗ[K] W) (B : Submodule K V) : Submodule K f.ker :=
  B.comap f.ker.subtype

abbrev KernelModulo (f : V →ₗ[K] W) (B : Submodule K V) :=
  f.ker ⧸ kernelBoundary f B

theorem finrank_kernelModulo_add [FiniteDimensional K V]
    (f : V →ₗ[K] W) (B : Submodule K V) :
    finrank K (KernelModulo f B) + finrank K (kernelBoundary f B) =
      finrank K f.ker := by
  exact (kernelBoundary f B).finrank_quotient_add_finrank

end GeneralKernelQuotient

variable {K : Type*} [Field K] {n r : ℕ}

def koszulSpace (q : Fin r → Forms K n 2) : Submodule K (Fin r → Forms K n 2) :=
  Submodule.span K (Set.range (koszulVector q))

abbrev incomingInKernel (q : Fin r → Forms K n 2) :=
  kernelBoundary (quadraticMultiplication q) (koszulSpace q)

abbrev QuarticHomology (q : Fin r → Forms K n 2) :=
  KernelModulo (quadraticMultiplication q) (koszulSpace q)

theorem finrank_incomingInKernel (q : Fin r → Forms K n 2)
    (hq : LinearIndependent K q) : finrank K (incomingInKernel q) = r.choose 2 := by
  unfold incomingInKernel kernelBoundary koszulSpace
  rw [(Submodule.comapSubtypeEquivOfLe (kernel_contains_koszul q)).finrank_eq]
  exact (finrank_span_eq_card (koszulVector_linearIndependent q hq)).trans card_generatorPair

theorem homology_add_pairs (q : Fin r → Forms K n 2)
    (hq : LinearIndependent K q) :
    finrank K (QuarticHomology q) + r.choose 2 =
      finrank K (LinearMap.ker (quadraticMultiplication q)) := by
  have h := finrank_kernelModulo_add (quadraticMultiplication q) (koszulSpace q)
  rwa [finrank_incomingInKernel q hq] at h

/-- The manuscript's degree-four Euler identity, on the actual multiplication complex. -/
theorem quartic_euler_identity (q : Fin r → Forms K n 2)
    (hq : LinearIndependent K q) :
    (finrank K (QuarticQuotient K n
      (Submodule.span K (Set.range (fun i => (q i).val)))) : ℤ) -
      (finrank K (QuarticHomology q) : ℤ) = Counts.chi n r := by
  have hhom := homology_add_pairs q hq
  have hcoker := quartic_quotient_add_rank q
  have hrank := (quadraticMultiplication q).finrank_range_add_finrank_ker
  have hdim : finrank K (Fin r → Forms K n 2) = r * (n + 1).choose 2 := by
    simp [Module.finrank_pi_fintype, finrank_quadrics]
  rw [hdim] at hrank
  unfold Counts.chi Counts.b4 Counts.b2
  zify at hhom hcoker hrank
  omega

/-- Zero homology means that only the forced Koszul relations occur. -/
theorem homology_zero_iff_rank (q : Fin r → Forms K n 2)
    (hq : LinearIndependent K q) :
    finrank K (QuarticHomology q) = 0 ↔
      finrank K (LinearMap.range (quadraticMultiplication q)) + r.choose 2 =
        r * (n + 1).choose 2 := by
  have hhom := homology_add_pairs q hq
  have hrank := (quadraticMultiplication q).finrank_range_add_finrank_ker
  have hdim : finrank K (Fin r → Forms K n 2) = r * (n + 1).choose 2 := by
    simp [Module.finrank_pi_fintype, finrank_quadrics]
  rw [hdim] at hrank
  omega

/-- Expected quotient dimension is equivalent to vanishing of one side of the
Euler identity. Which side must vanish is determined by the Euler sign. -/
theorem expected_quotient_iff_homology_or_quotient_zero (q : Fin r → Forms K n 2)
    (hq : LinearIndependent K q) :
    finrank K (QuarticQuotient K n
      (Submodule.span K (Set.range (fun i => (q i).val)))) = expectedDimension n r ↔
    finrank K (QuarticHomology q) = 0 ∨
      finrank K (QuarticQuotient K n
        (Submodule.span K (Set.range (fun i => (q i).val)))) = 0 := by
  have h := quartic_euler_identity q hq
  change _ = (Counts.chi n r).toNat ↔ _
  omega

end Quartic
