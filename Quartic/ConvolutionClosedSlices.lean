module

public import Quartic.IteratedSlicedCovectorCharts
public import Quartic.IteratedChartGeneric
public import Quartic.ConvolutionAllRange
public import Quartic.ConvolutionProfileBound
public import Quartic.BilinearImageMinors

@[expose] public section

/-!
# Closed sliced covector loci for the actual small convolution models

For every canonical configuration with 28≤m≤40, every closed kernel threshold
is excluded on a nonempty joint child-coefficient and auxiliary-slice open.
The proof includes all exact kernel ranks and actual prefix profiles, the
zero-kernel endpoint, and the impossibility of a full relation kernel.

The final finite homogeneous family consists of literal relation-matrix
minors, shared-child annihilation equations, and auxiliary linear slices.
Over an algebraically closed field its empty-fiber witness has precisely
the input type of HomogeneousEmptyFiberOpen. No unsliced dimension bound or
varying-presentation polynomial family is asserted here.
-/
noncomputable section
namespace Quartic.ClosedSlicedProfiles
open Module MvPolynomial IteratedBlockCharts IteratedCovectorCharts IteratedChartGeneric
open BilinearCoefficientKernel BilinearCovectorCharts
variable {K : Type*} [Field K] [Infinite K] {n B T q s : ℕ} {b : Fin n → ℕ}

/-- Every nonzero annihilating covector obeys the integer chart budget on one
shared coefficient/slice open, simultaneously at every exact kernel rank. -/
theorem generic_parameter_inequality
    (mu : (Fin B → K) →ₗ[K] (Fin (∑ i,b i) → K) →ₗ[K] (Fin T → K)) :
    ∃ P : MvPolynomial (Fin (finrank K (SharedCovectorPolynomial.Input K B T q s))) K,
      (∃ x : SharedCovectorPolynomial.Input K B T q s,
        eval (PolynomialBilinearCoordinates.coordinates K _ x) P ≠ 0) ∧
      ∀ x : SharedCovectorPolynomial.Input K B T q s,
        eval (PolynomialBilinearCoordinates.coordinates K _ x) P ≠ 0 →
        ∀ ell : Fin T → K,ell ≠ 0 →
        ((∀ i v,covector ell (mu (x.1 i) v)=0) ∧ (∀ j,covector ell (x.2 j)=0)) →
        let S := LinearMap.ker (relationMap mu ell)
        let r := fun i => (profile S i).val
        (q*((∑ i,b i)-finrank K S)+s:ℕ) ≤
          (parameterCount b r:ℤ)+(T:ℤ)-(finrank K (BilinearImage.image mu S):ℤ)-1 := by
  classical
  let C := Profiles b × Fin (T+1)
  have hc (c : C) :
      ∃ P : MvPolynomial (Fin (finrank K (SharedCovectorPolynomial.Input K B T q s))) K,
        (∃ x : SharedCovectorPolynomial.Input K B T q s,
          eval (PolynomialBilinearCoordinates.coordinates K _ x) P ≠ 0) ∧
        ∀ x : SharedCovectorPolynomial.Input K B T q s,
          eval (PolynomialBilinearCoordinates.coordinates K _ x) P ≠ 0 →
          ∀ ell : Fin T → K,ell ≠ 0 →
          (∀ i,finrank K (FilteredImage.initialPiece (fun i => Fin (b i) → K)
            ((LinearMap.ker (relationMap mu ell)).comap (coordinates K b).toLinearMap) i)=(c.1 i).val) →
          finrank K (BilinearImage.image mu (LinearMap.ker (relationMap mu ell)))=c.2.val →
          (parameterCount b (fun i => (c.1 i).val):ℤ)+(T:ℤ)-(c.2.val:ℤ)-1 <
            (q*((∑ i,b i)-(∑ i,(c.1 i).val))+s:ℕ) →
          ¬((∀ i v,covector ell (mu (x.1 i) v)=0) ∧ (∀ j,covector ell (x.2 j)=0)) := by
    by_cases hcount : (parameterCount b (fun i => (c.1 i).val):ℤ)+(T:ℤ)-(c.2.val:ℤ)-1 <
        (q*((∑ i,b i)-(∑ i,(c.1 i).val))+s:ℕ)
    · obtain ⟨P,hP,hgood⟩ := IteratedSlicedCovectorCharts.principal_open_excludes_profile_of_int_bound
        (e := c.2.val) (q := q) (s := s) mu (parameterCount b (fun i => (c.1 i).val):ℤ) le_rfl hcount
      exact ⟨P,hP,fun x hx ell hell hr he _ => hgood x hx ell hell hr (by omega)⟩
    · refine ⟨1,⟨0,by simp⟩,?_⟩
      intro x hx ell hell hr he hbad
      exact False.elim (hcount hbad)
  choose P hP hgood using hc
  have hne (c : C) : P c ≠ 0 := by
    obtain ⟨x,hx⟩ := hP c
    intro h
    simp [h] at hx
  obtain ⟨z₀,hz₀⟩ := nonempty_principal_intersection P hne
  refine ⟨∏ c,P c,⟨(PolynomialBilinearCoordinates.coordinates K _).symm z₀,?_⟩,?_⟩
  · simpa only [LinearEquiv.apply_symm_apply,map_prod] using
      Finset.prod_ne_zero_iff.mpr (fun c _ => hz₀ c)
  intro x hx ell hell hann
  dsimp only
  by_contra! hbad
  have he : finrank K (BilinearImage.image mu (LinearMap.ker (relationMap mu ell))) ≤ T := by
    simpa using (BilinearImage.image mu (LinearMap.ker (relationMap mu ell))).finrank_le
  let c : C := (profile (LinearMap.ker (relationMap mu ell)),
    ⟨finrank K (BilinearImage.image mu (LinearMap.ker (relationMap mu ell))),by omega⟩)
  have hxP : eval (PolynomialBilinearCoordinates.coordinates K _ x) (P c) ≠ 0 := by
    have hall : ∀ c,eval (PolynomialBilinearCoordinates.coordinates K _ x) (P c) ≠ 0 := by
      simpa only [map_prod,Finset.prod_ne_zero_iff,Finset.mem_univ,forall_const] using hx
    exact hall c
  apply hgood c x hxP ell hell (fun _ => rfl) rfl _ hann
  have hd := finrank_of_profile (LinearMap.ker (relationMap mu ell))
    (r := fun i => (profile (LinearMap.ker (relationMap mu ell)) i).val) (fun _ => rfl)
  simpa only [c,←hd] using hbad

end Quartic.ClosedSlicedProfiles


set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Quartic.ConvolutionClosedSlices
open Module MvPolynomial ProfileCertificate UniformEndpoint ConvolutionFreePieces
open PolynomialBilinearCoordinates ConvolutionProfileCoordinates
variable {K : Type*} [Field K]

section Transport
variable {U V W V' W' : Type*}
variable [AddCommGroup U] [Module K U]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']

 theorem image_conjugate (eV : V ≃ₗ[K] V') (eW : W ≃ₗ[K] W')
    (mu : U →ₗ[K] V →ₗ[K] W) (S : Submodule K V') :
    BilinearImage.image (conjugate eV eW mu) S =
      (BilinearImage.image mu (S.map eV.symm.toLinearMap)).map eW.toLinearMap := by
  simp only [BilinearImage.image, Submodule.map_iSup]
  congr 1
  funext u
  exact (Submodule.map_comp _ _ _).trans (congrArg (Submodule.map _) (Submodule.map_comp _ _ _))

 theorem image_precompose {U' : Type*} [AddCommGroup U'] [Module K U']
    (eU : U' ≃ₗ[K] U) (mu : U →ₗ[K] V →ₗ[K] W) (S : Submodule K V) :
    BilinearImage.image (mu.comp eU.toLinearMap) S = BilinearImage.image mu S := by
  exact eU.surjective.iSup_comp (fun u => S.map (mu u))
end Transport

abbrev Src (K : Type*) [Field K] (m : ℕ) (upper : Bool) :=
  Piece K (coreP (mixedCount m upper)+1) (freeW m (mixedCount m upper)) 1
abbrev Tgt (K : Type*) [Field K] (m : ℕ) (upper : Bool) :=
  Piece K (coreP (mixedCount m upper)+1) (freeW m (mixedCount m upper)) 3
abbrev Coeff (K : Type*) [Field K] (m : ℕ) (upper : Bool) :=
  Forms K (coreP (mixedCount m upper)+1+freeW m (mixedCount m upper)) 2
abbrev blocks (m : ℕ) (upper : Bool) :=
  ProfileChartBound.blockDimensions (2*((coreP (mixedCount m upper)+1)-1))
    (freeW m (mixedCount m upper))

def sourceCoordinates (m : ℕ) (upper : Bool)
    (ht : 2 ≤ coreP (mixedCount m upper)+1) :
    Src K m upper ≃ₗ[K] (Fin (∑ i,blocks m upper i) → K) :=
  (ConvolutionProfileCoordinates.coordinates ht).trans (IteratedCovectorCharts.coordinates K _)

/-- This is literal quotient multiplication in finite coordinates. -/
def actualMu (m : ℕ) (upper : Bool) (ht : 2 ≤ coreP (mixedCount m upper)+1) :
    (Fin (finrank K (Coeff K m upper)) → K) →ₗ[K]
      (Fin (∑ i,blocks m upper i) → K) →ₗ[K]
        (Fin (finrank K (Tgt K m upper)) → K) :=
  (conjugate (sourceCoordinates m upper ht) (PolynomialBilinearCoordinates.coordinates K _)
    (ConvolutionInitialImage.pieceBilinear (K := K)
      (t := coreP (mixedCount m upper)+1) (w := freeW m (mixedCount m upper)) (d := 1) (k := 2))).comp
      (PolynomialBilinearCoordinates.coordinates K (Coeff K m upper)).symm.toLinearMap

@[simp] theorem actualMu_apply (m : ℕ) (upper : Bool)
    (ht : 2 ≤ coreP (mixedCount m upper)+1)
    (f : Fin (finrank K (Coeff K m upper)) → K)
    (x : Fin (∑ i,blocks m upper i) → K) :
    actualMu m upper ht f x = PolynomialBilinearCoordinates.coordinates K _
      (ConvolutionFreeMultiplication.pieceMul
        ((PolynomialBilinearCoordinates.coordinates K (Coeff K m upper)).symm f)
        ((sourceCoordinates m upper ht).symm x)) := rfl

 theorem actual_image (m : ℕ) (upper : Bool) (ht : 2 ≤ coreP (mixedCount m upper)+1)
    (S : Submodule K (Fin (∑ i,blocks m upper i) → K)) :
    BilinearImage.image (actualMu m upper ht) S =
      (ConvolutionProfileImage.quadraticImage (S.map (sourceCoordinates m upper ht).symm.toLinearMap)).map
        (PolynomialBilinearCoordinates.coordinates K (Tgt K m upper)).toLinearMap := by
  rw [actualMu,image_precompose,image_conjugate]
  rfl

 theorem actual_image_finrank (m : ℕ) (upper : Bool)
    (ht : 2 ≤ coreP (mixedCount m upper)+1)
    (S : Submodule K (Fin (∑ i,blocks m upper i) → K)) :
    finrank K (BilinearImage.image (actualMu m upper ht) S) =
      finrank K (ConvolutionProfileImage.quadraticImage
        (S.map (sourceCoordinates m upper ht).symm.toLinearMap)) := by
  rw [actual_image,LinearEquiv.finrank_map_eq]

 theorem actual_profile (m : ℕ) (upper : Bool)
    (ht : 2 ≤ coreP (mixedCount m upper)+1)
    (S : Submodule K (Fin (∑ i,blocks m upper i) → K)) :
    (fun i => (IteratedChartGeneric.profile S i).val) =
      ranks ht (S.map (sourceCoordinates m upper ht).symm.toLinearMap) := by
  have hsub : S.comap (IteratedCovectorCharts.coordinates K (blocks m upper)).toLinearMap =
      (S.map (sourceCoordinates m upper ht).symm.toLinearMap).map
        (ConvolutionProfileCoordinates.coordinates ht).toLinearMap := by
    ext x
    constructor
    · intro hx
      refine ⟨(sourceCoordinates m upper ht).symm
        ((IteratedCovectorCharts.coordinates K (blocks m upper)) x),⟨_,hx,rfl⟩,?_⟩
      change (ConvolutionProfileCoordinates.coordinates ht)
        ((ConvolutionProfileCoordinates.coordinates ht).symm
          ((IteratedCovectorCharts.coordinates K (blocks m upper)).symm
            ((IteratedCovectorCharts.coordinates K (blocks m upper)) x)))=x
      rw [LinearEquiv.apply_symm_apply,LinearEquiv.symm_apply_apply]
    · rintro ⟨y,⟨z,hz,he⟩,hxy⟩
      subst y
      subst x
      change (IteratedCovectorCharts.coordinates K (blocks m upper))
        ((ConvolutionProfileCoordinates.coordinates ht)
          ((ConvolutionProfileCoordinates.coordinates ht).symm
            ((IteratedCovectorCharts.coordinates K (blocks m upper)).symm z))) ∈ S
      change z ∈ S at hz
      simpa only [LinearEquiv.apply_symm_apply] using hz
  funext i
  dsimp only [IteratedChartGeneric.profile, ConvolutionProfileCoordinates.ranks]
  rw [hsub]


 theorem blocks_sum (m : ℕ) (upper : Bool) :
    (∑ i,blocks m upper i)=totalA m (mixedCount m upper) := by
  simpa only [blocks,Nat.add_sub_cancel,coreA] using
    IteratedCovectorCharts.sum_blockDimensions m (mixedCount m upper)

 theorem target_eq_j_add (m : ℕ) (hm : 28 ≤ m) (upper : Bool) :
    (finrank K (Tgt K m upper):ℤ)=Counts.j m (upperEndpoint m) (mixedCount m upper)+
      (upperEndpoint m:ℤ)*(totalA m (mixedCount m upper):ℤ) := by
  rw [ConvolutionAllRange.endpoint_target_euler m hm upper]
  have hc := ConvolutionAllRange.endpoint_columns_range m hm upper
  rw [totalA_eq m _ hc.1 hc.2,Nat.cast_sub (by omega : mixedCount m upper ≤ 3*m)]
  unfold UniformScalar.targetCount Counts.j Counts.beta Counts.alpha
  push_cast
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
 theorem full_profile_target_verified : ∀ k : Fin 13,∀ upper : Bool,
    let m := k.val+28
    let c := FiniteCounts.mixedCount m upper
    Phi m c (coreA c) (freeW m c) (freeW m c) (freeW m c)=
      UniformScalar.targetCount m c := by
  decide +kernel

 theorem full_image_finrank [Infinite K] (m : ℕ) (hmlo : 28 ≤ m)
    (hmhi : m ≤ 40) (upper : Bool) :
    finrank K (ConvolutionProfileImage.quadraticImage (⊤ : Submodule K (Src K m upper)))=
      finrank K (Tgt K m upper) := by
  have hc := ConvolutionAllRange.endpoint_columns_range m hmlo upper
  obtain ⟨i,n₁,n₂,n₃,hi,hn₃,hn₂,hn₁,hd,_,hE⟩ :=
    ConvolutionProfileBound.exists_profile_bounds m (mixedCount m upper) hc.1
      (⊤ : Submodule K (Src K m upper))
  rw [finrank_top,ConvolutionAllRange.endpoint_source_finrank m hmlo upper] at hd
  have hieq : i=coreA (mixedCount m upper) := by unfold totalA at hd; omega
  have hn1eq : n₁=freeW m (mixedCount m upper) := by unfold totalA at hd; omega
  have hn2eq : n₂=freeW m (mixedCount m upper) := by unfold totalA at hd; omega
  have hn3eq : n₃=freeW m (mixedCount m upper) := by unfold totalA at hd; omega
  rw [hieq,hn1eq,hn2eq,hn3eq] at hE
  have hnum := full_profile_target_verified ⟨m-28,by omega⟩ upper
  have hm : m-28+28=m := by omega
  simp only [hm,←mixedCount_eq_table m (by omega)] at hnum
  rw [hnum,←ConvolutionAllRange.endpoint_target_euler (K := K) m hmlo upper] at hE
  exact le_antisymm (Submodule.finrank_le _) (by exact_mod_cast hE)

 theorem full_image_top [Infinite K] (m : ℕ) (hmlo : 28 ≤ m)
    (hmhi : m ≤ 40) (upper : Bool) :
    ConvolutionProfileImage.quadraticImage (⊤ : Submodule K (Src K m upper))=⊤ :=
  Submodule.eq_top_of_finrank_eq (full_image_finrank m hmlo hmhi upper)


 theorem actual_profile_image_bound [Infinite K] (m : ℕ) (hmlo : 28 ≤ m)
    (hmhi : m ≤ 40) (upper : Bool) (ht : 2 ≤ coreP (mixedCount m upper)+1)
    (S : Submodule K (Fin (∑ i,blocks m upper i) → K))
    (hdlo : 0 < finrank K S) (hdhi : finrank K S < totalA m (mixedCount m upper)) :
    (upperEndpoint m:ℤ)*(finrank K S:ℤ)+
      (IteratedBlockCharts.parameterCount (blocks m upper)
        (fun i => (IteratedChartGeneric.profile S i).val):ℤ)+
      min (((mixedCount m upper:ℤ)+4)*(finrank K S:ℤ))
        (Counts.j m (upperEndpoint m) (mixedCount m upper)) ≤
      (finrank K (BilinearImage.image (actualMu m upper ht) S):ℤ) := by
  let L := S.map (sourceCoordinates m upper ht).symm.toLinearMap
  have hd : finrank K L=finrank K S := (sourceCoordinates m upper ht).symm.finrank_map_eq S
  have hdloL : 0 < finrank K L := by rw [hd]; exact hdlo
  have hdhiL : finrank K L < totalA m (mixedCount m upper) := by rw [hd]; exact hdhi
  have hb := ConvolutionProfileChartBound.profile_integral_cell_image_bound (K := K) m hmlo hmhi upper ht L
    hdloL hdhiL
  have hc := ConvolutionProfileChartBound.parameterCount_le_profile_Cell (K := K) m (mixedCount m upper) ht L
  rw [actual_profile,actual_image_finrank]
  change _ ≤ (finrank K (ConvolutionProfileImage.quadraticImage L):ℤ)
  rw [hd] at hb
  have hfirst := add_le_add (le_refl ((upperEndpoint m:ℤ)*(finrank K S:ℤ))) hc
  exact (add_le_add hfirst (le_refl
    (min (((mixedCount m upper:ℤ)+4)*(finrank K S:ℤ))
      (Counts.j m (upperEndpoint m) (mixedCount m upper))))).trans hb

open BilinearCoefficientKernel BilinearCovectorCharts

/-- A nonzero actual target covector can never have the whole degree-one source
as its relation kernel. This endpoint does not use a genericity assertion. -/
 theorem actual_kernel_finrank_lt [Infinite K] (m : ℕ) (hmlo : 28 ≤ m)
    (hmhi : m ≤ 40) (upper : Bool) (ht : 2 ≤ coreP (mixedCount m upper)+1)
    (ell : Fin (finrank K (Tgt K m upper)) → K) (hell : ell ≠ 0) :
    finrank K (LinearMap.ker (relationMap (actualMu m upper ht) ell)) <
      totalA m (mixedCount m upper) := by
  let S := LinearMap.ker (relationMap (actualMu m upper ht) ell)
  have hdle : finrank K S ≤ totalA m (mixedCount m upper) := by
    simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin,blocks_sum] using S.finrank_le
  by_contra hlt
  change ¬ finrank K S < totalA m (mixedCount m upper) at hlt
  have hd : finrank K S=totalA m (mixedCount m upper) := by omega
  have htop : S=⊤ := Submodule.eq_top_of_finrank_eq (by
    simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin,blocks_sum] using hd)
  have hE := PolynomialSubspaceCovectorCharts.image_finrank_lt (actualMu m upper ht) S ell hell
    (kernel_image_annihilated _ _)
  rw [actual_image_finrank,htop,Submodule.map_top,(sourceCoordinates m upper ht).symm.range,
    full_image_finrank m hmlo hmhi upper] at hE
  omega

/-- The auxiliary slice count for the closed kernel threshold d. -/
def sliceCount (m : ℕ) (upper : Bool) (d : ℕ) : ℕ :=
  (Counts.j m (upperEndpoint m) (mixedCount m upper)-((mixedCount m upper:ℤ)+4)*(d:ℤ)).toNat

 theorem sliceCount_budget (m : ℕ) (upper : Bool) (d u : ℕ) (hdu : d ≤ u) :
    Counts.j m (upperEndpoint m) (mixedCount m upper) ≤
      min (((mixedCount m upper:ℤ)+4)*(u:ℤ))
        (Counts.j m (upperEndpoint m) (mixedCount m upper)) + sliceCount m upper d := by
  have h := Int.self_le_toNat (Counts.j m (upperEndpoint m) (mixedCount m upper)-
    ((mixedCount m upper:ℤ)+4)*(d:ℤ))
  have hdu' : (d:ℤ) ≤ u := by exact_mod_cast hdu
  dsimp only [sliceCount]
  rw [min_def]
  split_ifs with hmin
  · nlinarith
  · omega


/-- Actual child coefficients and auxiliary target vectors, in fixed bases. -/
abbrev SlicedInput (K : Type*) [Field K] (m : ℕ) (upper : Bool) (d : ℕ) :=
  SharedCovectorPolynomial.Input K (finrank K (Coeff K m upper))
    (finrank K (Tgt K m upper)) (upperEndpoint m) (sliceCount m upper d)

/-- One nonempty joint coefficient/slice open excludes the entire closed
kernel-threshold locus, including every exact-rank and profile boundary.
The statement is pointwise over K; when K is algebraically closed it is
geometric projective emptiness. No unsliced dimension statement is used. -/
theorem principal_open_closed_sliced_empty [Infinite K] (m : ℕ) (hmlo : 28 ≤ m)
    (hmhi : m ≤ 40) (upper : Bool) (ht : 2 ≤ coreP (mixedCount m upper)+1) (d : ℕ) :
    ∃ P : MvPolynomial (Fin (finrank K (SlicedInput K m upper d))) K,
      (∃ x : SlicedInput K m upper d,
        eval (PolynomialBilinearCoordinates.coordinates K _ x) P ≠ 0) ∧
      ∀ x : SlicedInput K m upper d,
        eval (PolynomialBilinearCoordinates.coordinates K _ x) P ≠ 0 →
        ∀ ell : Fin (finrank K (Tgt K m upper)) → K,
          d ≤ finrank K (LinearMap.ker (relationMap (actualMu m upper ht) ell)) →
          ((∀ i v,covector ell (actualMu m upper ht (x.1 i) v)=0) ∧
            (∀ j,covector ell (x.2 j)=0)) → ell=0 := by
  obtain ⟨P,hP,hgood⟩ := ClosedSlicedProfiles.generic_parameter_inequality
    (q := upperEndpoint m) (s := sliceCount m upper d) (actualMu (K := K) m upper ht)
  refine ⟨P,hP,?_⟩
  intro x hx ell hthreshold hann
  by_contra hell
  let S := LinearMap.ker (relationMap (actualMu m upper ht) ell)
  have hlt : finrank K S < totalA m (mixedCount m upper) :=
    actual_kernel_finrank_lt m hmlo hmhi upper ht ell hell
  have hthreshold' : d ≤ finrank K S := hthreshold
  have hineq := hgood x hx ell hell hann
  change ((upperEndpoint m)*((∑ i,blocks m upper i)-finrank K S)+sliceCount m upper d:ℕ) ≤
    (IteratedBlockCharts.parameterCount (blocks m upper)
      (fun i => (IteratedChartGeneric.profile S i).val):ℤ)+
        (finrank K (Tgt K m upper):ℤ)-
          (finrank K (BilinearImage.image (actualMu m upper ht) S):ℤ)-1 at hineq
  simp only [blocks_sum,Nat.cast_add,Nat.cast_mul,
    Nat.cast_sub (by omega : finrank K S ≤ totalA m (mixedCount m upper))] at hineq
  have hT := target_eq_j_add (K := K) m hmlo upper
  by_cases hpos : 0 < finrank K S
  · have hbound := actual_profile_image_bound m hmlo hmhi upper ht S hpos hlt
    have hslice := sliceCount_budget m upper d (finrank K S) hthreshold'
    nlinarith
  · have hzero : finrank K S=0 := by omega
    have hd : d=0 := by omega
    have hsum : (∑ i,(IteratedChartGeneric.profile S i).val)=0 := by
      have he := IteratedCovectorCharts.finrank_of_profile S
        (r := fun i => (IteratedChartGeneric.profile S i).val) (fun _ => rfl)
      exact he.symm.trans hzero
    have hr (i : Fin (freeW m (mixedCount m upper)+1)) :
        (IteratedChartGeneric.profile S i).val=0 := by
      have hi := Finset.single_le_sum
        (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (IteratedChartGeneric.profile S j).val)
        (Finset.mem_univ i)
      omega
    have hg : IteratedBlockCharts.parameterCount (blocks m upper)
        (fun i => (IteratedChartGeneric.profile S i).val)=0 := by
      simp only [IteratedBlockCharts.parameterCount,hr,zero_mul,ite_self,Finset.sum_const_zero,add_zero]
    have hj : 0 ≤ Counts.j m (upperEndpoint m) (mixedCount m upper) := by
      have h := (FiniteCounts.structural_dimension_signs m hmlo (by omega) upper).1
      simpa only [←mixedCount_eq_table m (by omega),←upperEndpoint_eq_table m (by omega)] using h.le
    have hs : (sliceCount m upper d:ℤ)=Counts.j m (upperEndpoint m) (mixedCount m upper) := by
      rw [hd,sliceCount]
      simp only [Nat.cast_zero,mul_zero,sub_zero,Int.toNat_of_nonneg hj]
    rw [hzero,hg,hs] at hineq
    have hE : (0:ℤ) ≤ finrank K (BilinearImage.image (actualMu m upper ht) S) := by positivity
    push_cast at hineq
    nlinarith

end Quartic.ConvolutionClosedSlices


set_option maxHeartbeats 200000
namespace Quartic.ClosedCovectorEquations
open Module MvPolynomial BilinearCoefficientKernel BilinearCovectorCharts
variable {K : Type*} [Field K] {a B T q s d : ℕ}

/-- The linear equation represented by a target vector. -/
def linearForm (y : Fin T → K) : Forms K T 1 :=
  ⟨∑ k,C (y k)*X k, by
    apply IsHomogeneous.sum
    intro k _
    exact (isHomogeneous_X K k).C_mul (y k)⟩

@[simp] theorem eval_linearForm (y ell : Fin T → K) :
    eval ell (linearForm y).val=covector ell y := by
  change (eval ell) (∑ k,C (y k)*X k)=covector ell y
  refine (MvPolynomial.eval_sum Finset.univ
    (fun k : Fin T => (C (y k)*X k : MvPolynomial (Fin T) K)) ell).trans ?_
  apply Eq.trans _ (BilinearCovectorCharts.covector_apply ell y).symm
  apply Finset.sum_congr rfl
  intro k _
  rw [MvPolynomial.eval_mul,MvPolynomial.eval_C,MvPolynomial.eval_X]
  exact mul_comm _ _

/-- All minors, shared child equations and auxiliary hyperplanes. Repeated
row/column selections are allowed, so no chart or exact-rank open is omitted. -/
abbrev Index (a B q s d : ℕ) :=
  ((Fin (a-d+1) → Fin a) × (Fin (a-d+1) → Fin B)) ⊕ ((Fin q × Fin a) ⊕ Fin s)

def degree : Index a B q s d → ℕ
  | .inl _ => a-d+1
  | .inr _ => 1

def equation (mu : (Fin B → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (x : SharedCovectorPolynomial.Input K B T q s) :
    (i : Index a B q s d) → Forms K T (degree i)
  | .inl uv => BilinearImageMinors.determinantForm
      (fun i j => linearForm (mu (Pi.single (uv.2 j) 1) (Pi.single (uv.1 i) 1)))
  | .inr (.inl iv) => linearForm (mu (x.1 iv.1) (Pi.single iv.2 1))
  | .inr (.inr h) => linearForm (x.2 h)

 theorem eval_minor (mu : (Fin B → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (x : SharedCovectorPolynomial.Input K B T q s)
    (u : Fin (a-d+1) → Fin a) (v : Fin (a-d+1) → Fin B) (ell : Fin T → K) :
    eval ell (equation mu x (.inl (u,v))).val =
      ((coefficientMatrix mu ell).submatrix u v).det := by
  change (eval ell) (Matrix.det _) = _
  rw [(eval ell).map_det]
  congr 1
  ext i j
  exact eval_linearForm _ _

/-- Vanishing of the finite homogeneous equation family is exactly the actual
closed kernel threshold and both groups of annihilation equations. -/
theorem equations_iff (mu : (Fin B → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (x : SharedCovectorPolynomial.Input K B T q s) (hd : d ≤ a) (ell : Fin T → K) :
    (∀ i : Index a B q s d,eval ell (equation mu x i).val=0) ↔
      d ≤ finrank K (LinearMap.ker (relationMap mu ell)) ∧
        ((∀ i v,covector ell (mu (x.1 i) v)=0) ∧ (∀ j,covector ell (x.2 j)=0)) := by
  classical
  have hr := coefficientMatrix_rank_add_kernel mu ell
  constructor
  · intro h
    have hmin : ∀ u : Fin (a-d+1) → Fin a,∀ v : Fin (a-d+1) → Fin B,
        ((coefficientMatrix mu ell).submatrix u v).det=0 := by
      intro u v
      simpa only [eval_minor] using h (.inl (u,v))
    have hlt := (BilinearImageMinors.rank_lt_iff_minors_zero (coefficientMatrix mu ell) (a-d+1)).mpr hmin
    refine ⟨by omega,⟨?_,?_⟩⟩
    · intro i v
      rw [←(Pi.basisFun K (Fin a)).sum_equivFun v]
      simp only [map_sum,map_smul,Pi.basisFun_apply,Pi.basisFun_equivFun]
      apply Finset.sum_eq_zero
      intro k _
      have hk : covector ell (mu (x.1 i) (Pi.single k 1))=0 := by
        simpa only [equation,eval_linearForm] using h (.inr (.inl (i,k)))
      rw [hk,smul_zero]
    · intro j
      simpa only [equation,eval_linearForm] using h (.inr (.inr j))
  · rintro ⟨hker,hQ,hZ⟩ i
    cases i with
    | inl uv =>
      rw [eval_minor]
      have hlt : (coefficientMatrix mu ell).rank < a-d+1 := by omega
      exact (BilinearImageMinors.rank_lt_iff_minors_zero _ _).mp hlt uv.1 uv.2
    | inr i =>
      cases i with
      | inl iv => simpa only [equation,eval_linearForm] using hQ iv.1 (Pi.single iv.2 1)
      | inr h => simpa only [equation,eval_linearForm] using hZ h

/-- Enumeration produces exactly the finite dependent family accepted by
HomogeneousEmptyFiberOpen. -/
def finiteDegree (a B q s d : ℕ) : Fin (Fintype.card (Index a B q s d)) → ℕ :=
  fun i => degree ((Fintype.equivFin (Index a B q s d)).symm i)

def finiteEquations (mu : (Fin B → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (x : SharedCovectorPolynomial.Input K B T q s) :
    (i : Fin (Fintype.card (Index a B q s d))) → Forms K T (finiteDegree a B q s d i) :=
  fun i => equation mu x ((Fintype.equivFin (Index a B q s d)).symm i)

 theorem finite_equations_iff (mu : (Fin B → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (x : SharedCovectorPolynomial.Input K B T q s) (hd : d ≤ a) (ell : Fin T → K) :
    (∀ i,eval ell (finiteEquations (d := d) mu x i).val=0) ↔
      d ≤ finrank K (LinearMap.ker (relationMap mu ell)) ∧
        ((∀ i v,covector ell (mu (x.1 i) v)=0) ∧ (∀ j,covector ell (x.2 j)=0)) := by
  rw [←equations_iff mu x hd ell]
  constructor
  · intro h i
    have hi := h (Fintype.equivFin (Index a B q s d) i)
    exact (congrArg (fun j : Index a B q s d => eval ell (equation mu x j).val=0)
      ((Fintype.equivFin (Index a B q s d)).symm_apply_apply i)).mp hi
  · intro h i
    exact h ((Fintype.equivFin (Index a B q s d)).symm i)

end Quartic.ClosedCovectorEquations


namespace Quartic.ConvolutionClosedSlices
open Module MvPolynomial ProfileCertificate UniformEndpoint ConvolutionFreePieces
open BilinearCoefficientKernel BilinearCovectorCharts ClosedCovectorEquations
variable {K : Type*} [Field K]

/-- The literal finite homogeneous equations have only the origin on one
nonempty joint Q/slice open. Over algebraically closed K this supplies the
geometric empty-fiber hypothesis, with L=K, of HomogeneousEmptyFiberOpen. -/
theorem principal_open_homogeneous_empty [IsAlgClosed K] (m : ℕ) (hmlo : 28 ≤ m)
    (hmhi : m ≤ 40) (upper : Bool) (ht : 2 ≤ coreP (mixedCount m upper)+1)
    (d : ℕ) (hd : d ≤ totalA m (mixedCount m upper)) :
    ∃ P : MvPolynomial (Fin (finrank K (SlicedInput K m upper d))) K,
      (∃ x : SlicedInput K m upper d,
        eval (PolynomialBilinearCoordinates.coordinates K _ x) P ≠ 0) ∧
      ∀ x : SlicedInput K m upper d,
        eval (PolynomialBilinearCoordinates.coordinates K _ x) P ≠ 0 →
        ∀ ell : Fin (finrank K (Tgt K m upper)) → K,
          (∀ i,aeval ell (finiteEquations (d := d) (actualMu m upper ht) x i).val=0) → ell=0 := by
  obtain ⟨P,hP,hgood⟩ := principal_open_closed_sliced_empty (K := K) m hmlo hmhi upper ht d
  refine ⟨P,hP,?_⟩
  intro x hx ell heq
  have hd' : d ≤ ∑ i,blocks m upper i := by rw [blocks_sum]; exact hd
  have hh := (finite_equations_iff (actualMu m upper ht) x hd' ell).mp
    (by simpa only [aeval_eq_eval] using heq)
  exact hgood x hx ell hh.1 hh.2

/-- A geometric witness with the precise finite dependent homogeneous family
needed for the existing finite multiplication certificate theorem. -/
theorem exists_homogeneous_empty_witness [IsAlgClosed K] (m : ℕ) (hmlo : 28 ≤ m)
    (hmhi : m ≤ 40) (upper : Bool) (ht : 2 ≤ coreP (mixedCount m upper)+1)
    (d : ℕ) (hd : d ≤ totalA m (mixedCount m upper)) :
    ∃ x : SlicedInput K m upper d,
      ∀ ell : Fin (finrank K (Tgt K m upper)) → K,
        (∀ i,aeval ell (finiteEquations (d := d) (actualMu m upper ht) x i).val=0) → ell=0 := by
  obtain ⟨_,⟨x,hx⟩,hgood⟩ := principal_open_homogeneous_empty (K := K) m hmlo hmhi upper ht d hd
  exact ⟨x,hgood x hx⟩

end Quartic.ConvolutionClosedSlices
