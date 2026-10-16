import FsFltz.Analysis.OriginalInitialPair
import FsFltz.Analysis.OriginalParameterRounding
import FsFltz.Geometry.LiouvilleCompletionFamilyCollar
import FsFltz.Geometry.CompletionPresentationMapGerms

/-!
# The fixed original pair while increasing its base coefficient

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–169, and
`eq:initialpair`, lines 301–348; `geometric-part-fsf-proof.tex`,
`lem:markedfamily`, lines 975–1009, and assembly, lines 2148–2153.
Any supplied original admissible profile is retained on the fixed literal
rounded domain and full far-fiber truncation. The Phase I collar constructors
supply both completed families; completed-family regularity is not input.
`exists_originalParameter_markedPairDeformation` retains the actual original
initial-pair data and both prescribed markings at every slice.
`exists_originalParameter_comparisonChain` supplies a one-step finite chain
between the constructed original initial pairs at the literal endpoint
coefficients. `OriginalParameterGrading` grades these same constructed
presentations using the retained actual map germs. Identifying an
independently supplied representation of the same pair is a separate question.
-/

noncomputable section
open scoped Manifold ContDiff
open Set

namespace FsFltz.InitialPairData

/-- Relabel an equal coefficient without changing the witnessed-pair tuple. -/
def castCoefficient {n : ℕ} {I : ToricInput n} {R K L Aminus A : ℝ} {m : RoundingChoice}
    (h : K = L) (S : InitialPairData I R K Aminus A m) :
    InitialPairData I R L Aminus A m := h ▸ S

@[simp] theorem castCoefficient_pair {n : ℕ} {I : ToricInput n}
    {R K L Aminus A : ℝ} {m : RoundingChoice} (h : K = L)
    (S : InitialPairData I R K Aminus A m) : (S.castCoefficient h).pair = S.pair := by
  subst L
  rfl

end FsFltz.InitialPairData

namespace FsFltz.Geometry
open SmoothManifold

set_option backward.isDefEq.respectTransparency false

/-- Joint smoothness of the literal original primitive along any affine
coefficient path, with a smooth extension for all real parameters. -/
theorem isSmoothIntervalFormFamily_lambdaK_affine {n : ℕ} (I : ToricInput n)
    (K L : ℝ) : (lgManifold n).IsSmoothIntervalFormFamily
      (fun t => lambdaKForm I ((1 - t.val) * K + t.val * L)) := by
  refine ⟨fun s => lambdaKForm I ((1 - s) * K + s * L), ?_, fun _ => rfl⟩
  intro a
  let c := chartAt (Model (2 * n)) a
  refine ⟨univ ×ˢ c.target, isOpen_univ.prod c.open_target,
    prod_mono (subset_univ _) Subset.rfl, ?_⟩
  have hzero : ContDiffOn ℝ ∞
      (fun p : ℝ × Model (2 * n) => (lgManifold n).formInChart a (lambda0Form n) p.2)
      (univ ×ˢ c.target) := (isSmoothForm_lambda0Form n a).comp contDiffOn_snd
    (fun p hp => hp.2)
  have hplane : ContDiffOn ℝ ∞
      (fun p : ℝ × Model (2 * n) =>
        (lgManifold n).formInChart a (superpotentialPlaneForm I) p.2)
      (univ ×ˢ c.target) := (isSmoothForm_superpotentialPlaneForm I a).comp contDiffOn_snd
    (fun p hp => hp.2)
  have hcoefficient : ContDiff ℝ ∞
      (fun p : ℝ × Model (2 * n) => (1 - p.1) * K + p.1 * L) :=
    ((contDiff_const.sub contDiff_fst).mul contDiff_const).add
      (contDiff_fst.mul contDiff_const)
  apply (hzero.add (hcoefficient.contDiffOn.smul hplane)).congr
  intro p _
  simp only [lambdaKForm, formInChart_add, formInChart_smul]
  rfl

namespace SmoothManifold

/-- A fixed smooth form has a joint smooth extension through all real times. -/
theorem isSmoothIntervalFormFamily_constant {d k : ℕ} (M : SmoothManifold d)
    (eta : M.Form k) (h : M.IsSmoothForm eta) :
    M.IsSmoothIntervalFormFamily (fun _ => eta) := by
  refine ⟨fun _ => eta, ?_, fun _ => rfl⟩
  intro a
  refine ⟨univ ×ˢ (chartAt (Model d) a).target,
    isOpen_univ.prod (chartAt (Model d) a).open_target,
    prod_mono (subset_univ _) Subset.rfl, ?_⟩
  exact (h a).comp contDiffOn_snd (fun _ hp => hp.2)

/-- A fixed smooth map is a jointly smooth interval map family. -/
theorem isSmoothIntervalMapFamily_constant {d e : ℕ} (M : SmoothManifold d)
    (N : SmoothManifold e) (f : M.Point → N.Point)
    (h : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞ f) :
    M.IsSmoothIntervalMapFamily N (fun _ => f) :=
  ⟨fun _ => f, ⟨univ, isOpen_univ, subset_univ _,
    (h.comp contMDiff_snd).contMDiffOn⟩, fun _ => rfl⟩

/-- A constant scalar is jointly smooth on any parameter interval. -/
theorem isSmoothIntervalScalarFamily_constant {d : ℕ} (M : SmoothManifold d)
    (c : ℝ) : M.IsSmoothIntervalScalarFamily (fun _ _ => c) := by
  refine ⟨fun _ _ => c, ?_, fun _ => rfl⟩
  intro a
  exact ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩

/-- A fixed smooth vector field has a joint smooth extension in the parameter. -/
theorem isSmoothIntervalVectorFieldFamily_constant {d : ℕ} (M : SmoothManifold d)
    (Z : (x : M.Point) → M.Tangent x) (h : M.IsSmoothVectorField Z) :
    M.IsSmoothIntervalVectorFieldFamily (fun _ => Z) := by
  refine ⟨fun _ => Z, ?_, fun _ => rfl⟩
  intro a
  refine ⟨univ ×ˢ (chartAt (Model d) a).target,
    isOpen_univ.prod (chartAt (Model d) a).open_target,
    prod_mono (subset_univ _) Subset.rfl, ?_⟩
  exact (h a).comp contDiffOn_snd (fun _ hp => hp.2)

/-- Pulling back a field through the identity smooth equivalence fixes it. -/
theorem pullbackVectorField_refl {d : ℕ} (M : SmoothManifold d)
    (Z : (x : M.Point) → M.Tangent x) :
    M.pullbackVectorField M (Diffeomorph.refl _ _ ∞) Z = Z := by
  funext x
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) id x (Z x) = Z x
  rw [mfderiv_id]
  rfl

end SmoothManifold

section Original

variable {n : ℕ} (I : ToricInput n)
  {Aamb R Afib K L Aminus A : ℝ} (hamb : AmbientEndBound I Aamb)
  (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
  (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K) (hKL : K ≤ L)
  (hfib : FiberEndBound I Aamb R Afib) (hlevels : Afib < Aminus)
  (m : RoundingChoice) (hm : GeometricAdmissibleRounding I R K Aminus A m)

local notation "E" => originalRoundedLiouvilleDomain I hamb hR hset hK hfib hlevels m hm
local notation "F" => originalRibbonLiouvilleDomain I hamb hR hfib hlevels m
  (And.left hm) (And.left (And.right hm))

/-- The same native rounded compact domain supports the actual Liouville
structure at every coefficient of the increasing affine path. Boundary
choices depend only on scalar regularity proofs and hence stay literally fixed. -/
def originalParameterLiouvilleStructure (t : Parameter) : LiouvilleStructure (E).domain := by
  have hpath : K ≤ (1 - t.val) * K + t.val * L := by
    nlinarith [mul_nonneg t.property.1 (sub_nonneg.mpr hKL)]
  have hnonneg : 0 ≤ K := (zero_le_one.trans (one_le_K0 I R hset.1 hset.2)).trans hK
  let alpha := lambdaKForm I ((1 - t.val) * K + t.val * L)
  have hs := isSmoothForm_lambdaKForm I ((1 - t.val) * K + t.val * L)
  have hω := isSymplecticOn_exteriorDerivative_lambdaKForm I (hnonneg.trans hpath)
  refine
    { primitive := alpha
      smooth_primitive := hs
      symplectic := ⟨hω.1, fun x _ => hω.2.1 x (mem_univ _),
        fun x _ => hω.2.2 x (mem_univ _)⟩
      field := (lgManifold n).liouvilleVector alpha
      smooth_field := (lgManifold n).isSmoothVectorField_liouvilleVector alpha hs
        (fun x => hω.2.2 x (mem_univ _))
      contraction := fun x _ => (lgManifold n).liouvilleVector_contraction alpha x
        ((lgManifold n).liouvilleEquation_exists alpha x (hω.2.2 x (mem_univ _)))
      outward := ?_ }
  intro x hx
  change 0 < differentialCovector (lgManifold n) (roundedDefiningFunction I R A m) x
    ((lgManifold n).liouvilleVector alpha x)
  rw [originalRoundedCompactDomain_frontier I hamb hR hset hK hfib hlevels m hm] at hx
  exact roundedDefiningFunction_increasing_parameter_path_outward I hamb hR hset hK hKL
    hfib hlevels m hm t.property x hx

/-- The fixed boundary inclusion retains the original fiber primitive for
every real coefficient, on the whole ribbon extension. -/
theorem exists_originalParameter_ribbonEmbedding :
    ∃ j : (F).domain.extension.SmoothEmbedding (E).domain.boundary,
      (∀ x, (E).domain.boundaryInclusion.map (j.map x) =
        (originalRibbonInAmbient I hamb hR hfib hlevels m hm.1 hm.2.1).map x) ∧
      ∀ t : Parameter, (F).domain.extension.pullback (E).domain.boundary j.map
        ((E).domain.boundaryForm
          (originalParameterLiouvilleStructure I hamb hR hset hK hKL hfib hlevels m hm t).primitive) =
        (F).liouville.primitive := by
  obtain ⟨j, hj, _⟩ := exists_originalRibbonBoundaryEmbedding I hamb hR hfib hlevels m
    hm.1 hm.2.1 hset hK hm
  refine ⟨j, hj, ?_⟩
  intro t
  change (F).domain.extension.pullback (E).domain.boundary j.map
    ((E).domain.boundary.pullback (lgManifold n) (E).domain.boundaryInclusion.map
      (lambdaKForm I ((1 - t.val) * K + t.val * L))) = (F).liouville.primitive
  rw [← (F).domain.extension.pullback_comp (E).domain.boundary (lgManifold n)
    (j.map.contMDiff.mdifferentiable (by simp))
    ((E).domain.boundaryInclusion.map.contMDiff.mdifferentiable (by simp))]
  rw [show (E).domain.boundaryInclusion.map ∘ j.map =
    (originalRibbonInAmbient I hamb hR hfib hlevels m hm.1 hm.2.1).map from funext hj]
  exact pullback_lambdaK_originalRibbon I hamb hR hfib hlevels m hm.1 hm.2.1 _

/-- Every slice of the fixed-carrier coefficient family has the prescribed
original ambient completion, built by the proved original absorption theorem. -/
def originalParameterAmbientCompletion (t : Parameter) :
    Completion (⟨(E).domain,
      originalParameterLiouvilleStructure I hamb hR hset hK hKL hfib hlevels m hm t⟩ :
        LiouvilleDomain (2 * n)) := by
  have hpath : K ≤ (1 - t.val) * K + t.val * L := by
    nlinarith [mul_nonneg t.property.1 (sub_nonneg.mpr hKL)]
  have hnonneg : 0 ≤ K := (zero_le_one.trans (one_le_K0 I R hset.1 hset.2)).trans hK
  exact originalRoundedCompletion I hamb hR hset (hK.trans hpath) hfib hlevels m
    (hm.mono_parameter I hnonneg hpath)

/-- The original entire ribbon and both inclusion/flow completion markings
are retained for each slice of the actual fixed-carrier coefficient family. -/
def originalParameterInitialPairData
    (j : (F).domain.extension.SmoothEmbedding (E).domain.boundary)
    (hj : ∀ x, (E).domain.boundaryInclusion.map (j.map x) =
      (originalRibbonInAmbient I hamb hR hfib hlevels m hm.1 hm.2.1).map x)
    (hp : ∀ t : Parameter, (F).domain.extension.pullback (E).domain.boundary j.map
      ((E).domain.boundaryForm
        (originalParameterLiouvilleStructure I hamb hR hset hK hKL hfib hlevels m hm t).primitive) =
      (F).liouville.primitive)
    (t : Parameter) : InitialPairData I R ((1 - t.val) * K + t.val * L) Aminus A m := by
  have hpath : K ≤ (1 - t.val) * K + t.val * L := by
    nlinarith [mul_nonneg t.property.1 (sub_nonneg.mpr hKL)]
  have hnonneg : 0 ≤ K := (zero_le_one.trans (one_le_K0 I R hset.1 hset.2)).trans hK
  let P : WitnessedPair n :=
    { ambientDomain := ⟨(E).domain,
        originalParameterLiouvilleStructure I hamb hR hset hK hKL hfib hlevels m hm t⟩
      ribbonDomain := (F)
      ribbonEmbedding := j
      witness := fun _ => 1
      smooth_witness := contMDiff_const
      positive_witness := fun _ => zero_lt_one
      ribbon_primitive := fun x _ => by simpa only [one_smul] using congrFun (hp t) x
      ambientCompletion := originalParameterAmbientCompletion I hamb hR hset hK hKL hfib hlevels m hm t
      ribbonCompletion := originalRibbonCompletion I hamb hR hfib hlevels m hm.1 hm.2.1 }
  let i : (E).domain.extension.SmoothEmbedding (lgManifold n) :=
    { map := ContMDiffMap.id
      embedding := Topology.IsEmbedding.id
      immersion := by
        intro x
        change Function.Injective (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) id x)
        rw [mfderiv_id]
        exact Function.injective_id }
  exact
    { pair := P
      ambient := originalCompletePrimitive I (hnonneg.trans hpath)
      domainEmbedding := i
      domain_image := image_id _
      ambientMarking := originalRoundedInclusionMarking I hamb hR hset (hK.trans hpath)
        hfib hlevels m (hm.mono_parameter I hnonneg hpath) P.ambientCompletion
      witness_one := fun _ => rfl
      fiber := originalFullFiberModel I hamb hR
      ribbonInFiber := originalRibbonInFiber I hamb hR hfib hlevels m hm.1 hm.2.1
      ribbon_image := originalRibbonLiouvilleDomain_image I hamb hR hfib hlevels m hm.1 hm.2.1
      ribbon_square := fun x _ => hj x
      fiberMarking := originalRibbonInclusionMarking I hamb hR hfib hlevels m hm.1 hm.2.1
      ribbon_nonempty := originalRibbonLiouvilleDomain_nonempty I hamb hR hfib hlevels m hm.1 hm.2.1 }

local notation "LC" => originalParameterLiouvilleStructure I hamb hR hset hK hKL hfib hlevels m hm
local notation "CC" => originalParameterAmbientCompletion I hamb hR hset hK hKL hfib hlevels m hm

/-- Assemble the actual original pair deformation from the compact and
completed presentations produced by the Liouville-family construction.
This transparent constructor retains the exact completion maps that can
subsequently carry the prescribed ambient grading. -/
def originalParameterPairDeformation
    (j : (F).domain.extension.SmoothEmbedding (E).domain.boundary)
    (hj : ∀ x, (E).domain.boundaryInclusion.map (j.map x) =
      (originalRibbonInAmbient I hamb hR hfib hlevels m hm.1 hm.2.1).map x)
    (hp : ∀ t : Parameter, (F).domain.extension.pullback (E).domain.boundary j.map
      ((E).domain.boundaryForm ((LC) t).primitive) = (F).liouville.primitive)
    (h : ℝ → DomainPresentationEquiv (E).domain (E).domain)
    (hB : ∀ t, (h t).boundaryEquiv = Diffeomorph.refl _ _ ∞)
    (hs : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, Model (2 * n)) ∞
      (fun p : ℝ × (E).domain.extension.Point => (h p.1).extensionEquiv p.2))
    (p : ∀ t : Parameter, CompletionPresentationEquiv ((CC) parameterZero) ((CC) t) (h t.val))
    (hcompleted : ((CC) parameterZero).ambient.manifold.IsSmoothIntervalFormFamily (fun t =>
      ((CC) parameterZero).ambient.manifold.pullback ((CC) t).ambient.manifold
        (p t).equiv ((CC) t).ambient.primitive))
    (hfield : ((CC) parameterZero).ambient.manifold.IsSmoothIntervalVectorFieldFamily (fun t =>
      ((CC) parameterZero).ambient.manifold.pullbackVectorField ((CC) t).ambient.manifold
        (p t).equiv ((CC) t).ambient.field)) : PairDeformation n := by
  let S := originalParameterInitialPairData I hamb hR hset hK hKL hfib hlevels m hm j hj hp
  let Ls := originalParameterLiouvilleStructure I hamb hR hset hK hKL hfib hlevels m hm
  let C := originalParameterAmbientCompletion I hamb hR hset hK hKL hfib hlevels m hm
  let CF := originalRibbonCompletion I hamb hR hfib hlevels m hm.1 hm.2.1
  have hL : (E).domain.extension.IsSmoothIntervalFormFamily (fun t => (Ls t).primitive) :=
    isSmoothIntervalFormFamily_lambdaK_affine I K L
  have hcompact : (E).domain.extension.IsSmoothIntervalFormFamily (fun t =>
      (E).domain.extension.pullback (E).domain.extension (h t.val).extensionEquiv (Ls t).primitive) :=
    (E).domain.extension.isSmoothIntervalFormFamily_pullback_one_of_contMDiff_family
      (E).domain.extension (fun t => (h t).extensionEquiv) hs (fun t => (Ls t).primitive) hL
  have hcompactfield : (E).domain.extension.IsSmoothIntervalVectorFieldFamily (fun t =>
      (E).domain.extension.pullbackVectorField (E).domain.extension (h t.val).extensionEquiv (Ls t).field) :=
    CompleteLiouvilleManifold.isSmoothIntervalVectorFieldFamily_pullback
      (E).domain.extension (fun t => (C t).ambient) (fun t => (h t.val).extensionEquiv) hcompact
  let hf := DomainPresentationEquiv.refl (F).domain
  let pf : CompletionPresentationEquiv CF CF hf :=
    { equiv := Diffeomorph.refl _ _ ∞
      compact_square := fun _ _ => rfl
      end_square := fun _ _ _ => rfl }
  have hμ : (F).domain.extension.IsSmoothIntervalFormFamily (fun _ : Parameter =>
      (F).domain.extension.pullback (F).domain.extension hf.extensionEquiv (F).liouville.primitive) := by
    change (F).domain.extension.IsSmoothIntervalFormFamily (fun _ : Parameter =>
      (F).domain.extension.pullback (F).domain.extension id (F).liouville.primitive)
    rw [(F).domain.extension.pullback_id]
    exact (F).domain.extension.isSmoothIntervalFormFamily_constant _ (F).liouville.smooth_primitive
  have hZ : (F).domain.extension.IsSmoothIntervalVectorFieldFamily (fun _ : Parameter =>
      (F).domain.extension.pullbackVectorField (F).domain.extension hf.extensionEquiv (F).liouville.field) := by
    change (F).domain.extension.IsSmoothIntervalVectorFieldFamily (fun _ : Parameter =>
      (F).domain.extension.pullbackVectorField (F).domain.extension
        (Diffeomorph.refl _ _ ∞) (F).liouville.field)
    rw [(F).domain.extension.pullbackVectorField_refl (F).liouville.field]
    exact (F).domain.extension.isSmoothIntervalVectorFieldFamily_constant _ (F).liouville.smooth_field
  have hcμ : CF.ambient.manifold.IsSmoothIntervalFormFamily (fun _ : Parameter =>
      CF.ambient.manifold.pullback CF.ambient.manifold pf.equiv CF.ambient.primitive) := by
    change CF.ambient.manifold.IsSmoothIntervalFormFamily (fun _ : Parameter =>
      CF.ambient.manifold.pullback CF.ambient.manifold id CF.ambient.primitive)
    rw [CF.ambient.manifold.pullback_id]
    exact CF.ambient.manifold.isSmoothIntervalFormFamily_constant _ CF.ambient.smooth_primitive
  have hcZ : CF.ambient.manifold.IsSmoothIntervalVectorFieldFamily (fun _ : Parameter =>
      CF.ambient.manifold.pullbackVectorField CF.ambient.manifold pf.equiv CF.ambient.field) := by
    change CF.ambient.manifold.IsSmoothIntervalVectorFieldFamily (fun _ : Parameter =>
      CF.ambient.manifold.pullbackVectorField CF.ambient.manifold
        (Diffeomorph.refl _ _ ∞) CF.ambient.field)
    rw [CF.ambient.manifold.pullbackVectorField_refl CF.ambient.field]
    exact CF.ambient.manifold.isSmoothIntervalVectorFieldFamily_constant _ CF.ambient.smooth_field
  have hjs : (F).domain.extension.IsSmoothIntervalMapFamily (E).domain.boundary
      (fun t x => (h t.val).boundaryEquiv.invFun (j.map (hf.extensionEquiv x))) := by
    have he : (fun (t : Parameter) x => (h t.val).boundaryEquiv.invFun (j.map (hf.extensionEquiv x))) =
        (fun (_ : Parameter) x => j.map x) := by
      funext t x
      rw [hB]
      rfl
    rw [he]
    exact (F).domain.extension.isSmoothIntervalMapFamily_constant (E).domain.boundary j.map j.map.contMDiff
  let Q : PairDeformation n :=
    { pair := fun t => (S t).pair
      ambientPresentation := fun t => h t.val
      ribbonPresentation := fun _ => hf
      ambientCompletionPresentation := p
      ribbonCompletionPresentation := fun _ => pf
      ambientPrimitive_smooth := hcompact
      ribbonPrimitive_smooth := hμ
      ambientField_smooth := hcompactfield
      ribbonField_smooth := hZ
      ribbonEmbedding_smooth := hjs
      witness_smooth := (E).domain.boundary.isSmoothIntervalScalarFamily_constant 1
      completedAmbientPrimitive_smooth := hcompleted
      completedRibbonPrimitive_smooth := hcμ
      completedAmbientField_smooth := hfield
      completedRibbonField_smooth := hcZ }
  exact Q

include hamb hR hset hK hKL hfib hlevels hm in
/-- The actual original family has coherent completed presentations and
native local smooth germs after the specified inclusion marking. The map
germs follow from the constructed inward collar and the actual original
Liouville flows, rather than from joint regularity of the markings. -/
theorem exists_originalParameter_presentations_with_mapGerms :
    ∃ j : (F).domain.extension.SmoothEmbedding (E).domain.boundary,
    ∃ hj : ∀ x, (E).domain.boundaryInclusion.map (j.map x) =
      (originalRibbonInAmbient I hamb hR hfib hlevels m hm.1 hm.2.1).map x,
    ∃ hp : ∀ t : Parameter, (F).domain.extension.pullback (E).domain.boundary j.map
      ((E).domain.boundaryForm ((LC) t).primitive) = (F).liouville.primitive,
    ∃ h : ℝ → DomainPresentationEquiv (E).domain (E).domain,
      (∀ t, (h t).boundaryEquiv = Diffeomorph.refl _ _ ∞) ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, Model (2 * n)) ∞
        (fun p : ℝ × (E).domain.extension.Point => (h p.1).extensionEquiv p.2) ∧
      ∃ p : ∀ t : Parameter, CompletionPresentationEquiv ((CC) parameterZero) ((CC) t) (h t.val),
        ((CC) parameterZero).ambient.manifold.IsSmoothIntervalFormFamily (fun t =>
          ((CC) parameterZero).ambient.manifold.pullback ((CC) t).ambient.manifold
            (p t).equiv ((CC) t).ambient.primitive) ∧
        ((CC) parameterZero).ambient.manifold.IsSmoothIntervalVectorFieldFamily (fun t =>
          ((CC) parameterZero).ambient.manifold.pullbackVectorField ((CC) t).ambient.manifold
            (p t).equiv ((CC) t).ambient.field) ∧
        IntrinsicSmoothBundle.HasSmoothManifoldTargetFamilyOn
          ((CC) parameterZero).ambient.manifold (lgManifold n) univ
          (fun t x =>
            (originalParameterInitialPairData I hamb hR hset hK hKL hfib hlevels m hm j hj hp t).ambientMarking.equiv
              ((p t).equiv x)) := by
  obtain ⟨j, hj, hp⟩ := exists_originalParameter_ribbonEmbedding I hamb hR hset hK hKL hfib hlevels m hm
  let S := originalParameterInitialPairData I hamb hR hset hK hKL hfib hlevels m hm j hj hp
  obtain ⟨h, hB, hs, _, _, p, hcompleted, hfield, δ, hδ, hend⟩ :=
    (E).domain.exists_smooth_completionFamily_with_inward_end_square (LC)
      (isSmoothIntervalFormFamily_lambdaK_affine I K L) (CC)
  have hα : (lgManifold n).IsSmoothIntervalFormFamily (fun t : Parameter =>
      (lgManifold n).pullback (S t).ambient.toCompleteLiouvilleManifold.manifold
        (Diffeomorph.refl 𝓘(ℝ, Model (2 * n)) (lgManifold n).Point ∞)
        (S t).ambient.toCompleteLiouvilleManifold.primitive) := by
    change (lgManifold n).IsSmoothIntervalFormFamily (fun t : Parameter =>
      (lgManifold n).pullback (lgManifold n) id
        (lambdaKForm I ((1 - t.val) * K + t.val * L)))
    simp_rw [(lgManifold n).pullback_id]
    exact isSmoothIntervalFormFamily_lambdaK_affine I K L
  have hflow := IntrinsicSmoothBundle.completeFlowInCoordinates_realGerms_of_smooth_primitive
    (fun t => (S t).ambient.toCompleteLiouvilleManifold) (lgManifold n)
    (fun _ => Diffeomorph.refl 𝓘(ℝ, Model (2 * n)) (lgManifold n).Point ∞) univ hα
  refine ⟨j, hj, hp, h, hB, hs, p, hcompleted, hfield, ?_⟩
  apply ((CC) parameterZero).hasSmoothManifoldTargetFamilyOn_of_compact_and_flow_germs
    (lgManifold n)
    (fun t x => (S t).ambientMarking.equiv ((p t).equiv x))
    (fun t x => (h t).extensionEquiv x) (E).domain.boundaryInclusion.map
    (fun t r x => (S t).ambient.completeFlow.flow r x)
    hs (E).domain.boundaryInclusion.map.contMDiff hflow δ hδ
  · intro t x hx
    change (S t).ambientMarking.equiv ((p t).equiv (((CC) parameterZero).inclusion.map x)) = _
    rw [(p t).compact_square x hx]
    have hy : (h t.val).extensionEquiv x ∈ (E).domain.carrier := by
      rw [← (h t.val).carrier]
      exact ⟨x, hx, rfl⟩
    exact (S t).ambientMarking.inclusion ⟨(h t.val).extensionEquiv x, hy⟩
  · intro t x r hr
    change (S t).ambientMarking.equiv ((p t).equiv (((CC) parameterZero).endMap (x, r))) = _
    rw [hend t x r hr]
    have hx : (E).domain.boundaryInclusion.map x ∈ (E).domain.carrier := by
      apply (E).domain.compact.isClosed.frontier_subset
      rw [← (E).domain.boundary_range]
      exact ⟨x, rfl⟩
    have hi : (S t).ambientMarking.equiv
        (((CC) t).inclusion.map ((E).domain.boundaryInclusion.map x)) =
        (E).domain.boundaryInclusion.map x :=
      (S t).ambientMarking.inclusion ⟨(E).domain.boundaryInclusion.map x, hx⟩
    have hf : (S t).ambientMarking.equiv (((CC) t).endMap (x, r)) =
        (S t).ambient.completeFlow.flow r ((S t).ambientMarking.equiv
          (((CC) t).inclusion.map ((E).domain.boundaryInclusion.map x))) :=
      (S t).ambientMarking.flow_induced x r
    exact hf.trans (congrArg (fun y => (S t).ambient.completeFlow.flow r y) hi)

include hamb hR hset hK hKL hfib hlevels hm in
/-- The actual original initial-pair data form one completed smooth pair
deformation. Every slice retains both prescribed inclusion/flow markings,
the arbitrary supplied rounding profile, and the entire nonempty ribbon.
This version uses the original completion presentations, without localization
of the endpoint tuples. -/
theorem exists_originalParameter_markedPairDeformation :
    ∃ S : (t : Parameter) → InitialPairData I R ((1 - t.val) * K + t.val * L) Aminus A m,
    ∃ Q : PairDeformation n, Q.pair = fun t => (S t).pair := by
  obtain ⟨j, hj, hp, h, hB, hs, p, hcompleted, hfield, _⟩ :=
    exists_originalParameter_presentations_with_mapGerms I hamb hR hset hK hKL hfib hlevels m hm
  exact ⟨originalParameterInitialPairData I hamb hR hset hK hKL hfib hlevels m hm j hj hp,
    originalParameterPairDeformation I hamb hR hset hK hKL hfib hlevels m hm
      j hj hp h hB hs p hcompleted hfield, rfl⟩

include hamb hR hset hK hKL hfib hlevels hm in
/-- The increasing-coefficient family is a literal permitted step between
actual original initial pairs at its two endpoint coefficients. Both
endpoint data retain the supplied profile, full ribbon, and both markings. -/
theorem exists_originalParameter_comparisonStep :
    ∃ P : InitialPairData I R K Aminus A m,
    ∃ T : InitialPairData I R L Aminus A m,
    ∃ Q : PairDeformation n, Q.source = P.pair ∧ Q.target = T.pair ∧
      Nonempty (ComparisonStep n P.pair T.pair) := by
  obtain ⟨S, Q, hQ⟩ := exists_originalParameter_markedPairDeformation
    I hamb hR hset hK hKL hfib hlevels m hm
  have hzero : (1 - parameterZero.val) * K + parameterZero.val * L = K := by
    simp [parameterZero]
  have hone : (1 - parameterOne.val) * K + parameterOne.val * L = L := by
    simp [parameterOne]
  let P := (S parameterZero).castCoefficient hzero
  let T := (S parameterOne).castCoefficient hone
  have hsource : Q.source = P.pair := by
    simp only [P, PairDeformation.source, hQ, InitialPairData.castCoefficient_pair]
  have htarget : Q.target = T.pair := by
    simp only [T, PairDeformation.target, hQ, InitialPairData.castCoefficient_pair]
  refine ⟨P, T, Q, hsource, htarget, ?_⟩
  rw [← hsource, ← htarget]
  exact ⟨.deformation Q⟩

include hamb hR hset hK hKL hfib hlevels hm in
/-- The first original parameter operation supplies a finite chain of one
actual deformation, with literal original initial-pair endpoints. -/
theorem exists_originalParameter_comparisonChain :
    ∃ P : InitialPairData I R K Aminus A m,
    ∃ T : InitialPairData I R L Aminus A m,
    ∃ C : ComparisonChain P.pair T.pair, C.length = 1 := by
  obtain ⟨P, T, Q, hs, ht, _⟩ := exists_originalParameter_comparisonStep
    I hamb hR hset hK hKL hfib hlevels m hm
  refine ⟨P, T, ?_⟩
  rw [← hs, ← ht]
  exact ⟨Quiver.Path.nil.cons (.deformation Q), rfl⟩

end Original

end FsFltz.Geometry
