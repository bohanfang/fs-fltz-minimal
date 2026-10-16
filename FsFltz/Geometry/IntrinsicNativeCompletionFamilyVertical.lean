import FsFltz.Geometry.IntrinsicNativeCompletionFamilySliceEquiv
import FsFltz.Geometry.IntrinsicFormFamilyGluing
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Smooth vertical primitives on the original completed total atlas

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–169, and
`sec:lean`, lines 788–814. A jointly smooth covector on the native tangent
bundle of the original total family restricts to its exact original slice
primitives. The extension can have parameter components: no false
zero-parameter gluing across the moving collar is asserted.

The conclusion is native `ContMDiff ∞` regularity in the closed parameter
model. Correspondence with a single real open `C^∞` extension germ at each
parameter endpoint remains a separate foundational bridge.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology Bundle

namespace FsFltz.Geometry.SmoothManifold

/-- Chartwise interval regularity of an actual one-form family gives a
smooth scalar evaluation on the native spatial tangent bundle, jointly
with the interval parameter, including its boundary points. -/
theorem IsSmoothIntervalFormFamily.contMDiff_tangentEvaluation
    {d : ℕ} {N : SmoothManifold d} {α : Parameter → N.Form 1}
    (hα : N.IsSmoothIntervalFormFamily α) :
    ContMDiff ((𝓡∂ 1).prod (𝓘(ℝ, Model d)).tangent) 𝓘(ℝ, ℝ) ∞
      (fun p : Parameter × TangentBundle 𝓘(ℝ, Model d) N.Point =>
        α p.1 p.2.proj (fun _ => p.2.2)) := by
  obtain ⟨β, hβ, heq⟩ := hα
  intro p
  let x := p.2.proj
  let c := chartAt (Model d) x
  let e := trivializationAt (Model d) (TangentSpace 𝓘(ℝ, Model d)) x
  have hx : x ∈ c.source := mem_chart_source _ _
  have he : p.2 ∈ e.source := by
    rw [TangentBundle.trivializationAt_source]
    exact hx
  have hv : ContMDiffAt ((𝓡∂ 1).prod (𝓘(ℝ, Model d)).tangent)
      𝓘(ℝ, Model d) ∞ (fun q : Parameter × TangentBundle 𝓘(ℝ, Model d) N.Point =>
        (e q.2).2) p :=
    contMDiffAt_snd.comp p
      ((e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds he)).comp p contMDiffAt_snd)
  have hbase : ContMDiffAt ((𝓡∂ 1).prod (𝓘(ℝ, Model d)).tangent)
      𝓘(ℝ, Model d) ∞ (fun q : Parameter × TangentBundle 𝓘(ℝ, Model d) N.Point =>
        c q.2.proj) p :=
    ((contMDiffOn_chart (I := 𝓘(ℝ, Model d)) (x := x)).contMDiffAt
      (c.open_source.mem_nhds hx)).comp p
        ((Bundle.contMDiff_proj (TangentSpace 𝓘(ℝ, Model d))).contMDiffAt.comp p
          contMDiffAt_snd)
  have ht : ContMDiffAt ((𝓡∂ 1).prod (𝓘(ℝ, Model d)).tangent)
      𝓘(ℝ, ℝ) ∞ (fun q : Parameter × TangentBundle 𝓘(ℝ, Model d) N.Point =>
        q.1.val) p := contMDiff_subtypeVal_Icc.contMDiffAt.comp p contMDiffAt_fst
  obtain ⟨U, hU, hcover, hcoeff⟩ := hβ x
  have hpU : (p.1.val, c x) ∈ U := hcover ⟨p.1.property, c.map_source hx⟩
  have hc : ContMDiffAt ((𝓡∂ 1).prod (𝓘(ℝ, Model d)).tangent)
      𝓘(ℝ, Model d [⋀^Fin 1]→L[ℝ] ℝ) ∞
      (fun q : Parameter × TangentBundle 𝓘(ℝ, Model d) N.Point =>
        N.formInChart x (β q.1.val) (c q.2.proj)) p :=
    (hcoeff.contDiffAt (hU.mem_nhds hpU)).contMDiffAt.comp p (ht.prodMk_space hbase)
  let L := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := Model d) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  have hs := (L.symm.contDiff.contMDiff.contMDiffAt.comp p hc).clm_apply hv
  apply hs.congr_of_eventuallyEq
  have hproj : ContMDiff ((𝓡∂ 1).prod (𝓘(ℝ, Model d)).tangent)
      𝓘(ℝ, Model d) ∞
      (fun q : Parameter × TangentBundle 𝓘(ℝ, Model d) N.Point => q.2.proj) :=
    (Bundle.contMDiff_proj (TangentSpace 𝓘(ℝ, Model d))).comp contMDiff_snd
  have hn : ∀ᶠ q in 𝓝 p, q.2.proj ∈ c.source :=
    hproj.continuous.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hx)
  filter_upwards [hn] with q hq
  dsimp only [Function.comp_def]
  rw [heq q.1]
  have hev : (e q.2).2 =
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c q.2.proj q.2.2 := by
    rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hq,
      TangentBundle.continuousLinearMapAt_trivializationAt hq]
    rfl
  rw [hev]
  change α q.1 q.2.proj (fun _ => q.2.2) =
    N.formInChart x (α q.1) (c q.2.proj)
      (fun _ => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c q.2.proj q.2.2)
  dsimp only [formInChart]
  rw [c.left_inv hq]
  have hd := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) x).symm_comp_deriv hq
  change (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c.symm (c q.2.proj)).comp
    (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c q.2.proj) =
      ContinuousLinearMap.id ℝ (Model d) at hd
  change _ = α q.1 q.2.proj (fun _ =>
    ((mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c.symm (c q.2.proj)).comp
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c q.2.proj)) q.2.2)
  rw [hd]
  rfl

end FsFltz.Geometry.SmoothManifold

namespace FsFltz.Geometry

section NativeCovectors

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace X]
  (I : ModelWithCorners ℝ E H) [ChartedSpace H X]

/-- A genuine covector on the whole native total tangent fiber. Its
restriction to a spatial slice uses only that slice's differential.
Parameter components are allowed. -/
def nativeTotalCovector {d : ℕ} (N : SmoothManifold d)
    (p : X → Parameter) (q : X → N.Point) (α : Parameter → N.Form 1) :
    (z : X) → TangentSpace I z [⋀^Fin 1]→L[ℝ] ℝ := fun z =>
  (α (p z) (q z)).compContinuousLinearMap (mfderiv I 𝓘(ℝ, Model d) q z)

variable [IsManifold I ∞ X]

/-- The total covector's scalar evaluation is a smooth function on the
actual native tangent bundle. This gives intrinsic section regularity in
every chart, rather than smoothness only after replacing the source atlas. -/
theorem contMDiff_nativeTotalCovector_eval {d : ℕ} (N : SmoothManifold d)
    (p : X → Parameter) (q : X → N.Point) (α : Parameter → N.Form 1)
    (hp : ContMDiff I (𝓡∂ 1) ∞ p)
    (hq : ContMDiff I 𝓘(ℝ, Model d) ∞ q)
    (hα : N.IsSmoothIntervalFormFamily α) :
    ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞
      (fun v : TangentBundle I X => nativeTotalCovector I N p q α v.proj
        (fun _ => v.2)) := by
  have hp' : ContMDiff I.tangent (𝓡∂ 1) ∞
      (fun v : TangentBundle I X => p v.proj) :=
    hp.comp (Bundle.contMDiff_proj (TangentSpace I))
  have hq' : ContMDiff I.tangent (𝓘(ℝ, Model d)).tangent ∞ (tangentMap I 𝓘(ℝ, Model d) q) :=
    hq.contMDiff_tangentMap (by simp)
  exact hα.contMDiff_tangentEvaluation.comp (hp'.prodMk hq')

omit [IsManifold I ∞ X] in
/-- The total covector restriction is the literal spatial pullback. The
chain rule compares the actual slice inclusion with the actual total map. -/
theorem nativeTotalCovector_restrict {a d : ℕ}
    (M : SmoothManifold a) (N : SmoothManifold d)
    (p : X → Parameter) (q : X → N.Point) (α : Parameter → N.Form 1)
    (hq : ContMDiff I 𝓘(ℝ, Model d) ∞ q)
    (i : M.Point → X) (hi : ContMDiff 𝓘(ℝ, Model a) I ∞ i)
    (t : Parameter) (hp : ∀ x, p (i x) = t) (x : M.Point) :
    (nativeTotalCovector I N p q α (i x)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, Model a) I i x) = M.pullback N (q ∘ i) (α t) x := by
  rw [nativeTotalCovector, hp x]
  have hd := mfderiv_comp x (hq.mdifferentiableAt (by simp))
    (hi.mdifferentiableAt (by simp))
  ext vs
  change α t (q (i x)) (fun j =>
      mfderiv I 𝓘(ℝ, Model d) q (i x)
        (mfderiv 𝓘(ℝ, Model a) I i x (vs j))) =
    α t (q (i x)) (fun j => mfderiv 𝓘(ℝ, Model a) 𝓘(ℝ, Model d) (q ∘ i) x (vs j))
  rw [hd]
  rfl

end NativeCovectors

end FsFltz.Geometry

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

include hboundary hmix hq htransport in
/-- The exact original completed primitives have a smooth total covector
extension on the original completion-family atlas. Its restriction is an
equality on the full actual spatial tangent fiber at every slice point.
The witness uses this same `Q`, `C`, `q`, and produced `Λ`. -/
theorem exists_ambientNativeTotalCovector_extension_eq :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    letI := totalFamily_isManifold hδ C hboundary hzero hjoint hmix
    ∃ Ω : (z : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) →
        TangentSpace (familyModel (k + 1)) z [⋀^Fin 1]→L[ℝ] ℝ,
      Ω = nativeTotalCovector (familyModel (k + 1))
        Q.source.ambientCompletion.ambient.manifold
        (parameter (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val))
        q Q.completedPrimitive ∧
      ContMDiff (familyModel (k + 1)).tangent 𝓘(ℝ, ℝ) ∞
        (fun v : TangentBundle (familyModel (k + 1))
            (TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) =>
          Ω v.proj (fun _ => v.2)) ∧
      ∀ t, letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
        ∀ x, (Ω (sliceIn (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) t x)).compContinuousLinearMap
          (mfderiv 𝓘(ℝ, Model (k + 1)) (familyModel (k + 1))
            (sliceIn (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) t) x) =
              Λ t x := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let := totalFamily_isManifold hδ C hboundary hzero hjoint hmix
  let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
  let Ω := nativeTotalCovector (familyModel (k + 1))
    Q.source.ambientCompletion.ambient.manifold (parameter c) q Q.completedPrimitive
  refine ⟨Ω, rfl, contMDiff_nativeTotalCovector_eval (familyModel (k + 1))
    Q.source.ambientCompletion.ambient.manifold (parameter c) q Q.completedPrimitive
    (contMDiff_parameter hδ C hboundary hzero hjoint hmix) hq
    Q.completedAmbientPrimitive_smooth, ?_⟩
  intro t
  let := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
  intro x
  rw [nativeTotalCovector_restrict (familyModel (k + 1))
    (completionManifold hδ (C t) (hemb t) (hC t) (hboundary t) (hinv t) (hzero t))
    Q.source.ambientCompletion.ambient.manifold (parameter c) q Q.completedPrimitive hq
    (sliceIn c t) (contMDiff_sliceIn hδ C hemb hC hboundary hinv hzero hjoint hmix t)
    t (parameter_sliceIn c t) x]
  exact congrFun (htransport t) x

include hboundary hmix hq htransport in
/-- The exact original primitives have a smooth total covector extension.
The canonical witness is retained by the stronger producer above. -/
theorem exists_ambientNativeTotalCovector_extension :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    letI := totalFamily_isManifold hδ C hboundary hzero hjoint hmix
    ∃ Ω : (z : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) →
        TangentSpace (familyModel (k + 1)) z [⋀^Fin 1]→L[ℝ] ℝ,
      ContMDiff (familyModel (k + 1)).tangent 𝓘(ℝ, ℝ) ∞
        (fun v : TangentBundle (familyModel (k + 1))
            (TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) =>
          Ω v.proj (fun _ => v.2)) ∧
      ∀ t, letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
        ∀ x, (Ω (sliceIn (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) t x)).compContinuousLinearMap
          (mfderiv 𝓘(ℝ, Model (k + 1)) (familyModel (k + 1))
            (sliceIn (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) t) x) =
              Λ t x := by
  obtain ⟨Ω, _, hsmooth, hrestriction⟩ :=
    Q.exists_ambientNativeTotalCovector_extension_eq hδ C hemb hC hboundary hinv
      hzero hjoint hmix Λ q hq htransport
  exact ⟨Ω, hsmooth, hrestriction⟩

end FsFltz.Geometry.PairDeformation
