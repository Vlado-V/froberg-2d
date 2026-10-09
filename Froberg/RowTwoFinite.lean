module

public import Froberg.RowTwoRange
public import Froberg.QuotientConvolution

@[expose] public section

/-! A finite row-two witness from two actual convolution constructions.
No preceding-degree endpoint assertion is used. -/
noncomputable section
namespace Froberg
open Module
variable {K : Type*} [Field K] [Infinite K]
variable {h m s D rF rE : ℕ}
attribute [local instance] tensorGroup

theorem exists_row_two_from_convolution
    (hm : 0 < m) (hs : 1 ≤ s)
    (A : Submodule K (Poly K h)) (hA : A ≤ Forms K h 1)
    [Module.Finite K A]
    (hDlo : finrank K (EndpointQuotient K h 1 A) ≤ D)
    (hDhi : D ≤ finrank K (Forms K h 2))
    (hcountF : convolutionBlockCount (finrank K A) (s+1) s * (m+(s+1)+s-2).choose s ≤ rF)
    (hcountE : convolutionBlockCount (finrank K (EndpointQuotient K h 1 A)) (s+2) (s-1) *
      (m+(s+2)+(s-1)-2).choose (s-1) ≤ rE) :
    ∃ (o : Fin rF → Forms K h 1) (f : Fin rF → Forms K m s)
      (W : Submodule K (Forms K h 2)) (O : Fin rE → W) (g : Fin rE → Forms K m (s-1)),
      finrank K W = D ∧
      Function.Surjective ((biformFamilyMap (x := 1) (y := s) o f).coprod
        (vectorFormFamilyToDegree (show (s-1)+(s+1)=s+s by omega) (fun i => (O i).val) g)) := by
  obtain ⟨o,f,hF⟩ := exists_convolution_family_of_count (K := K) (W := A)
    (by omega : 0 < s+1) hm hcountF
  have hF' : Function.Surjective (vectorFormFamilyMap (t := s) o f) := by
    simpa only [Nat.add_sub_cancel] using hF
  let U := endpointProducts K h 1 A
  obtain ⟨W,O,g,hWD,hG⟩ := exists_lifted_convolution_family (K := K)
    U.mkQ U.mkQ_surjective hDlo hDhi (by omega : 0 < s+2) hm hcountE
  have hG' : Function.Surjective (vectorFormFamilyMap (t := s+1) (fun i => U.mkQ (O i).val) g) := by
    simpa only [show s+2-1=s+1 by omega] using hG
  refine ⟨fun i => homogeneousInclusion A hA (o i),f,W,O,g,hWD,?_⟩
  exact row_two_coprod_surjective A hA o f hF' (fun i => (O i).val) g _ hG'

end Froberg
