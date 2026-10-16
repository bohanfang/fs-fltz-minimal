import FsFltz.Geometry.IntrinsicNativeCompletionFamilySliceEquiv
import FsFltz.Geometry.IntrinsicNativeCompletionFamilyFields
import FsFltz.Geometry.FamilyLiouvilleNeighborhood

/-!
# Smooth vertical fields on original completed total families

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–169, and
`sec:lean`, lines 788–814. Smooth interval field coefficients give an actual
smooth tangent section. A parameter-preserving total diffeomorphism transports
that section to the original total atlas; its slice restriction is identified
with the original form-determined Liouville field.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.SmoothManifold

/-- An extendible interval field family is jointly smooth as a native tangent
section, retaining the interval manifold structure at both endpoints. -/
theorem IsSmoothIntervalVectorFieldFamily.contMDiff_tangentSection
    {d : ℕ} {M : SmoothManifold d}
    {Z : (t : Parameter) → (x : M.Point) → M.Tangent x}
    (hZ : M.IsSmoothIntervalVectorFieldFamily Z) :
    ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
      (fun p : Parameter × M.Point =>
        (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point)) := by
  obtain ⟨W, hW, heq⟩ := hZ
  intro p
  obtain ⟨U, hU, hcover, hcoeff⟩ := hW p.2
  have hp : (p.1.val, chartAt (Model d) p.2 p.2) ∈ U :=
    hcover ⟨p.1.property, (chartAt (Model d) p.2).map_source (mem_chart_source _ _)⟩
  have hs := M.contMDiffAt_familySection_of_chart W p.2 (p.1.val, p.2)
    (mem_chart_source _ _) (hcoeff.contDiffAt (hU.mem_nhds hp))
  have hc : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
      (fun p : Parameter × M.Point => (p.1.val, p.2)) :=
    contMDiff_subtypeVal_Icc.prodMap contMDiff_id
  have h := hs.comp p hc.contMDiffAt
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun p => by simp only [Function.comp_def, heq])

/-- The zero parameter lift of the actual interval field is a smooth field
on the interval product, including its parameter boundary. -/
theorem IsSmoothIntervalVectorFieldFamily.contMDiff_verticalLift
    {d : ℕ} {M : SmoothManifold d}
    {Z : (t : Parameter) → (x : M.Point) → M.Tangent x}
    (hZ : M.IsSmoothIntervalVectorFieldFamily Z) :
    ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, Model d)) ((𝓡∂ 1).prod 𝓘(ℝ, Model d)).tangent ∞
      (fun p : Parameter × M.Point =>
        (⟨p, (0, Z p.1 p.2)⟩ : TangentBundle ((𝓡∂ 1).prod 𝓘(ℝ, Model d))
          (Parameter × M.Point))) := by
  have ht : ContMDiff (𝓡∂ 1) (𝓡∂ 1).tangent ∞
      (fun t : Parameter => (⟨t, 0⟩ : TangentBundle (𝓡∂ 1) Parameter)) :=
    Bundle.contMDiff_zeroSection ℝ (TangentSpace (𝓡∂ 1))
  exact contMDiff_equivTangentBundleProd_symm.comp
    ((ht.comp contMDiff_fst).prodMk hZ.contMDiff_tangentSection)

end FsFltz.Geometry.SmoothManifold

namespace FsFltz.Geometry.IntrinsicCompletionGluing

section Transport

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  {d : ℕ} (N : SmoothManifold d)
  (F : Diffeomorph I (familyModel d) X (Parameter × N.Point) ∞)
  (Z : (t : Parameter) → (x : N.Point) → N.Tangent x)

/-- Pull back the zero parameter lift by the actual total diffeomorphism. -/
def pulledVerticalField (x : X) : TangentSpace I x :=
  mfderiv (familyModel d) I F.symm (F x) (0, Z (F x).1 (F x).2)

/-- The transported field is a smooth section on the original source atlas. -/
theorem contMDiff_pulledVerticalField
    (hZ : N.IsSmoothIntervalVectorFieldFamily Z) :
    ContMDiff I I.tangent ∞
      (fun x : X => (⟨x, pulledVerticalField N F Z x⟩ : TangentBundle I X)) := by
  have h := (F.symm.contMDiff.contMDiff_tangentMap (m := ∞) (by simp)).comp
    (hZ.contMDiff_verticalLift.comp F.contMDiff)
  convert h using 1
  funext x
  exact Bundle.TotalSpace.ext (F.symm_apply_apply x).symm (HEq.rfl)

omit [IsManifold I ∞ X] in
/-- The derivative of a slice recovers the pulled field whenever the same
comparison takes that slice field to the zero-parameter reference field. -/
theorem mfderiv_slice_pulledVerticalField
    {a : ℕ} (M : SmoothManifold a) (s : M.Point → X)
    (hs : ContMDiff 𝓘(ℝ, Model a) I ∞ s)
    (V : (x : M.Point) → M.Tangent x)
    (hV : ∀ x, mfderiv 𝓘(ℝ, Model a) (familyModel d) (F ∘ s) x (V x) =
      (0, Z (F (s x)).1 (F (s x)).2)) (x : M.Point) :
    mfderiv 𝓘(ℝ, Model a) I s x (V x) = pulledVerticalField N F Z (s x) := by
  have he : F.symm ∘ (F ∘ s) = s := by ext y; exact F.symm_apply_apply (s y)
  have h := mfderiv_comp x
    (F.symm.mdifferentiable (by simp) (F (s x)))
    ((F.contMDiff.comp hs).mdifferentiable (by simp) x)
  rw [he] at h
  change _ = mfderiv (familyModel d) I F.symm (F (s x)) _
  rw [h]
  change mfderiv (familyModel d) I F.symm (F (s x))
    (mfderiv 𝓘(ℝ, Model a) (familyModel d) (F ∘ s) x (V x)) = _
  rw [hV x]

end Transport

end FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.SmoothManifold

/-- Composing with an actual diffeomorphism can be cancelled in a field
transport equation; the result uses its genuine inverse derivative. -/
theorem mfderiv_eq_pullbackVectorField_of_composite
    {a d e : ℕ} (M : SmoothManifold a) (N : SmoothManifold d) (P : SmoothManifold e)
    (f : M.Point → N.Point) (hf : ContMDiff 𝓘(ℝ, Model a) 𝓘(ℝ, Model d) ∞ f)
    (p : N.SmoothEquiv P) (V : (x : M.Point) → M.Tangent x)
    (Z : (x : P.Point) → P.Tangent x)
    (hV : ∀ x, mfderiv 𝓘(ℝ, Model a) 𝓘(ℝ, Model e) (p ∘ f) x (V x) = Z (p (f x)))
    (x : M.Point) :
    mfderiv 𝓘(ℝ, Model a) 𝓘(ℝ, Model d) f x (V x) =
      N.pullbackVectorField P p Z (f x) := by
  have he : p.symm ∘ (p ∘ f) = f := by ext y; exact p.symm_apply_apply (f y)
  have h := mfderiv_comp x (p.symm.mdifferentiable (by simp) (p (f x)))
    ((p.contMDiff.comp hf).mdifferentiable (by simp) x)
  rw [he] at h
  rw [h]
  change mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) p.symm (p (f x))
    (mfderiv 𝓘(ℝ, Model a) 𝓘(ℝ, Model e) (p ∘ f) x (V x)) = _
  rw [hV x]
  rfl

end FsFltz.Geometry.SmoothManifold

namespace FsFltz.Geometry.PairDeformation
open IntrinsicCompletionGluing

variable {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  (Q : PairDeformation n)
  {δ : ℝ} (hδ : 0 < δ)
  (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : ∀ t, IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
  (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞
    (C t) (Half δ (IntrinsicBoundary.Point k M)))
  (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
  (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)
  (hzero : ∀ t x, C t (0, x) = x.val)
  (hjoint : IsOpenEmbedding (totalCollar
    (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
  (hmix : HasRealMixedGerms (δ := δ) C)
  (Λ : ∀ t, (completionManifold hδ (C t) (hemb t) (hC t)
    (hboundary t) (hinv t) (hzero t)).Form 1)
  (q : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) →
    Q.source.ambientCompletion.ambient.manifold.Point)
  (hq : letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiff (familyModel (k + 1)) 𝓘(ℝ, Model (2 * n)) ∞ q)
  (htransport : ∀ t, (completionManifold hδ (C t) (hemb t) (hC t)
    (hboundary t) (hinv t) (hzero t)).pullback Q.source.ambientCompletion.ambient.manifold
    (q ∘ sliceIn (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) t)
    (Q.completedPrimitive t) = Λ t)


include hq htransport in
/-- The original form-determined slice fields are the restrictions of one
smooth vertical tangent section on the actual original total-family atlas.
Smoothness here is in the native closed-interval model. -/
theorem exists_ambientNativeTotalField_extension_eq
    (hdim : k + 1 = 2 * n)
    (hΛnd : ∀ t x, (completionManifold hδ (C t) (hemb t) (hC t)
      (hboundary t) (hinv t) (hzero t)).Nondegenerate
      ((completionManifold hδ (C t) (hemb t) (hC t)
        (hboundary t) (hinv t) (hzero t)).exteriorDerivative (Λ t)) x)
    (F : letI := totalFamilyChartedSpace hδ C hzero hjoint
      Diffeomorph (familyModel (k + 1)) (familyModel (2 * n))
        (TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val))
        (Parameter × Q.source.ambientCompletion.ambient.manifold.Point) ∞)
    (hF : ∀ z, F z = (parameter (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) z, q z)) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    letI := totalFamily_isManifold hδ C hboundary hzero hjoint hmix
    ∃ V : (z : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) →
        TangentSpace (familyModel (k + 1)) z,
      V = pulledVerticalField Q.source.ambientCompletion.ambient.manifold F
        (fun t => Q.source.ambientCompletion.ambient.manifold.pullbackVectorField
          (Q.pair t).ambientCompletion.ambient.manifold
          (Q.ambientCompletionPresentation t).equiv (Q.pair t).ambientCompletion.ambient.field) ∧
      ContMDiff (familyModel (k + 1)) (familyModel (k + 1)).tangent ∞
        (fun z => (⟨z, V z⟩ : TangentBundle (familyModel (k + 1))
          (TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))) ∧
      ∀ t, letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
        ∀ x, mfderiv 𝓘(ℝ, Model (k + 1)) (familyModel (k + 1))
          (sliceIn (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) t) x
          ((completionManifold hδ (C t) (hemb t) (hC t)
            (hboundary t) (hinv t) (hzero t)).liouvilleVector (Λ t) x) =
          V (sliceIn (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) t x) := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let := totalFamily_isManifold hδ C hboundary hzero hjoint hmix
  let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
  let N := Q.source.ambientCompletion.ambient.manifold
  let Z := fun t => N.pullbackVectorField (Q.pair t).ambientCompletion.ambient.manifold
    (Q.ambientCompletionPresentation t).equiv (Q.pair t).ambientCompletion.ambient.field
  refine ⟨pulledVerticalField N F Z, rfl,
    contMDiff_pulledVerticalField N F Z Q.completedAmbientField_smooth, ?_⟩
  intro t
  let := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
  let A := completionManifold hδ (C t) (hemb t) (hC t) (hboundary t) (hinv t) (hzero t)
  have hs := contMDiff_sliceIn hδ C hemb hC hboundary hinv hzero hjoint hmix t
  have hqs := hq.comp hs
  have hf := Q.map_liouvilleVector_ambientNativeTotalMap hdim hδ C hemb hC hboundary
    hinv hzero hjoint hmix Λ q hq htransport hΛnd t
  have href := A.mfderiv_eq_pullbackVectorField_of_composite N
    (Q.pair t).ambientCompletion.ambient.manifold (q ∘ sliceIn c t) hqs
    (Q.ambientCompletionPresentation t).equiv (A.liouvilleVector (Λ t))
    (Q.pair t).ambientCompletion.ambient.field hf
  apply mfderiv_slice_pulledVerticalField N F Z A (sliceIn c t) hs
    (A.liouvilleVector (Λ t))
  intro x
  have he : F ∘ sliceIn c t = fun x => (t, q (sliceIn c t x)) := by
    funext x
    rw [Function.comp_apply, hF, parameter_sliceIn]
  rw [he]
  erw [mfderiv_prodMk (f := fun _ : A.Point => t)
    (mdifferentiableAt_const) (hqs.mdifferentiable (by simp) x)]
  change (mfderiv 𝓘(ℝ, Model (k + 1)) (𝓡∂ 1) (fun _ : A.Point => t) x
      (A.liouvilleVector (Λ t) x),
    mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (q ∘ sliceIn c t) x
      (A.liouvilleVector (Λ t) x)) = _
  rw [mfderiv_const, zero_apply, href x, hF, parameter_sliceIn]
  rfl


include hq htransport in
/-- The original form-determined slice fields are the restrictions of one
smooth vertical tangent section on the actual original total-family atlas.
Smoothness here is in the native closed-interval model. -/
theorem exists_ambientNativeTotalField_extension
    (hdim : k + 1 = 2 * n)
    (hΛnd : ∀ t x, (completionManifold hδ (C t) (hemb t) (hC t)
      (hboundary t) (hinv t) (hzero t)).Nondegenerate
      ((completionManifold hδ (C t) (hemb t) (hC t)
        (hboundary t) (hinv t) (hzero t)).exteriorDerivative (Λ t)) x)
    (F : letI := totalFamilyChartedSpace hδ C hzero hjoint
      Diffeomorph (familyModel (k + 1)) (familyModel (2 * n))
        (TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val))
        (Parameter × Q.source.ambientCompletion.ambient.manifold.Point) ∞)
    (hF : ∀ z, F z = (parameter (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) z, q z)) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    letI := totalFamily_isManifold hδ C hboundary hzero hjoint hmix
    ∃ V : (z : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) →
        TangentSpace (familyModel (k + 1)) z,
      ContMDiff (familyModel (k + 1)) (familyModel (k + 1)).tangent ∞
        (fun z => (⟨z, V z⟩ : TangentBundle (familyModel (k + 1))
          (TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))) ∧
      ∀ t, letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
        ∀ x, mfderiv 𝓘(ℝ, Model (k + 1)) (familyModel (k + 1))
          (sliceIn (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) t) x
          ((completionManifold hδ (C t) (hemb t) (hC t)
            (hboundary t) (hinv t) (hzero t)).liouvilleVector (Λ t) x) =
          V (sliceIn (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) t x) := by
  obtain ⟨V, _, hV, hs⟩ :=
    Q.exists_ambientNativeTotalField_extension_eq hδ C hemb hC hboundary hinv hzero hjoint hmix
      Λ q hq htransport hdim hΛnd F hF
  exact ⟨V, hV, hs⟩

end FsFltz.Geometry.PairDeformation
