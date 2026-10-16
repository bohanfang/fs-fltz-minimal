import FsFltz.Geometry.OriginalBundleCompletionMarkingFieldRegularity
import FsFltz.Geometry.IntrinsicFormFamilyGluing

/-!
# Source primitive and actual flow germs on a retained local base

Source: `geoemtric-part-fsf.tex`, smoothness convention, lines 119–122;
`def:pair`, lines 143–158; `def:chain`, lines 163–199; `g:initial`,
lines 374–384; and `sec:lean`, lines 788–814. Source coordinates exist
only on the retained relative-open parameter base. An ordinary real
extension of the transported primitives is smooth on a neighborhood of
that base times the source manifold. Inverting its spatial contraction
matrix produces a smooth field on an open nondegeneracy neighborhood.
Actual slice symplecticity, the Liouville equation, and ODE uniqueness
then give real germs of the actual finite-time source flows and markings.
No coordinate equivalence, geometric law, or completed source section is
required outside the retained base.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology Classical
open Set Filter Bundle Topology
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry
namespace SmoothManifold

/-- Local ordinary primitive regularity and actual nondegeneracy produce
an open native neighborhood carrying the actual form-determined field. -/
theorem exists_liouvilleVector_familyOn_neighborhood_at {d : ℕ} (M : SmoothManifold d)
    (alpha : ℝ → M.Form 1) {Ω : Set (ℝ × M.Point)} (hΩ : IsOpen Ω)
    (halpha : M.IsSmoothFormFamilyOn alpha Ω)
    (p : ℝ × M.Point) (hpΩ : p ∈ Ω)
    (hnd : M.Nondegenerate (M.exteriorDerivative (alpha p.1)) p.2) :
    ∃ V : Set (ℝ × M.Point), IsOpen V ∧ p ∈ V ∧
      (∀ q ∈ V, M.Nondegenerate (M.exteriorDerivative (alpha q.1)) q.2) ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
        (fun q : ℝ × M.Point =>
          (⟨q.2, M.liouvilleVector (alpha q.1) q.2⟩ :
            TangentBundle 𝓘(ℝ, Model d) M.Point)) V := by
  let c := chartAt (Model d) p.2
  let U : Set (ℝ × Model d) := (univ ×ˢ c.target) ∩
    (fun ty : ℝ × Model d => (ty.1, c.symm ty.2)) ⁻¹' Ω
  have hU : IsOpen U := M.isOpen_inverseProductChart_preimage p.2 hΩ
  have hf := halpha p.2
  change ContDiffOn ℝ ∞ (fun ty => M.formInChart p.2 (alpha ty.1) ty.2) U at hf
  let f := fun ty : ℝ × Model d => M.formInChart p.2 (alpha ty.1) ty.2
  let B := fun ty : ℝ × Model d => extDeriv (fun z => f (ty.1, z)) ty.2
  let A := fun ty : ℝ × Model d => chartContraction (B ty)
  let b := fun ty : ℝ × Model d => (chartOneFormEquiv d).symm (f ty)
  have hB : ContDiffOn ℝ ∞ B U := contDiffOn_spatialExtDeriv f U hU hf
  have hcur : ContDiff ℝ ∞ (ContinuousAlternatingMap.curryLeft :
      (Model d [⋀^Fin 2]→L[ℝ] ℝ) → Model d →L[ℝ] Model d [⋀^Fin 1]→L[ℝ] ℝ) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := Model d [⋀^Fin 2]→L[ℝ] ℝ)
      (F := Model d →L[ℝ] Model d [⋀^Fin 1]→L[ℝ] ℝ)
      (ContinuousAlternatingMap.curryLeftLI
        (𝕜 := ℝ) (E := Model d) (F := ℝ) (n := 1)).toContinuousLinearMap
  have hA : ContDiffOn ℝ ∞ A U := contDiffOn_const.clm_comp (hcur.comp_contDiffOn hB)
  have hb : ContDiffOn ℝ ∞ b U := (chartOneFormEquiv d).symm.contDiff.comp_contDiffOn hf
  have hres (ty : ℝ × Model d) (hty : ty ∈ U) (hy : ty.2 ∈ c.target) :
      M.formInChart p.2 (M.exteriorDerivative (alpha ty.1)) ty.2 = B ty := by
    have hs : ContDiffAt ℝ ∞ (fun z => f (ty.1, z)) ty.2 :=
      (hf.contDiffAt (hU.mem_nhds hty)).comp ty.2 (contDiffAt_const.prodMk contDiffAt_id)
    exact M.formInChart_exteriorDerivative_of_contDiffAt (alpha ty.1) p.2 ty.2 hy hs
  let W := (U ∩ (univ ×ˢ c.target)) ∩ A ⁻¹' {T | T.IsInvertible}
  have hW : IsOpen W := (hA.continuousOn.mono inter_subset_left).isOpen_inter_preimage
    (hU.inter (isOpen_univ.prod c.open_target))
    ContinuousLinearMap.isOpen_setOfPred_isInvertible
  have hactual (ty : ℝ × Model d) (hty : ty ∈ W) :
      M.Nondegenerate (M.exteriorDerivative (alpha ty.1)) (c.symm ty.2) := by
    apply M.nondegenerate_of_formInChart _ p.2 hty.1.2.2
    rw [hres ty hty.1.1 hty.1.2.2]
    exact nondegenerate_of_chartContraction_invertible (B ty) hty.2
  have hAi : ContDiffOn ℝ ∞ (fun ty => (A ty).inverse) W := by
    intro ty hty
    exact hty.2.contDiffAt_map_inverse.comp_contDiffWithinAt ty
      (hA ty hty.1.1 |>.mono (fun _ hw => hw.1.1))
  have hfield : ContDiffOn ℝ ∞ (fun ty : ℝ × Model d =>
      M.vectorInChart p.2 (M.liouvilleVector (alpha ty.1)) ty.2) W := by
    apply (hAi.clm_apply (hb.mono (fun _ hw => hw.1.1))).congr
    intro ty hty
    have he := M.liouvilleVector_chart_eq (alpha ty.1) p.2 hty.1.2.2 (hactual ty hty)
    rw [hres ty hty.1.1 hty.1.2.2] at he
    exact he
  let g := fun q : ℝ × M.Point => (q.1, c q.2)
  let V := (univ ×ˢ c.source) ∩ g ⁻¹' W
  have hg : ContinuousOn g (univ ×ˢ c.source) :=
    continuousOn_fst.prodMk (c.continuousOn.comp continuousOn_snd (fun _ hq => hq.2))
  have hV : IsOpen V := hg.isOpen_inter_preimage (isOpen_univ.prod c.open_source) hW
  have hps : p.2 ∈ c.source := mem_chart_source _ _
  have hpt : c p.2 ∈ c.target := c.map_source hps
  have hpU : (p.1, c p.2) ∈ U :=
    ⟨⟨mem_univ _, hpt⟩, by simpa only [mem_preimage, c.left_inv hps] using hpΩ⟩
  have hpW : (p.1, c p.2) ∈ W := by
    refine ⟨⟨hpU, mem_univ _, hpt⟩, ?_⟩
    change (chartContraction (B (p.1, c p.2))).IsInvertible
    rw [← hres _ hpU hpt]
    apply chartContraction_invertible
    apply M.nondegenerate_formInChart _ p.2 hpt
    change M.Nondegenerate (M.exteriorDerivative (alpha p.1)) (c.symm (c p.2))
    simpa only [c.left_inv hps] using hnd
  refine ⟨V, hV, ⟨⟨mem_univ _, hps⟩, hpW⟩, ?_, ?_⟩
  · intro q hq
    have hn := hactual (g q) hq.2
    simpa only [g, c.left_inv hq.1.2] using hn
  · intro q hq
    exact (M.contMDiffAt_familySection_of_chart
      (fun t => M.liouvilleVector (alpha t)) p.2 q hq.1.2
      (hfield.contDiffAt (hW.mem_nhds hq.2))).contMDiffWithinAt


/-- Joint primitive regularity near an arbitrary retained real parameter
set gives an open smooth field neighborhood. Nondegeneracy is used only
on that retained set; no off-base symplectic law is assumed. -/
theorem exists_liouvilleVector_familyOn_neighborhood {d : ℕ} (M : SmoothManifold d)
    (alpha : ℝ → M.Form 1) {Ω : Set (ℝ × M.Point)} (hΩ : IsOpen Ω)
    (halpha : M.IsSmoothFormFamilyOn alpha Ω) (A : Set ℝ)
    (hcover : A ×ˢ univ ⊆ Ω)
    (hnd : ∀ r ∈ A, ∀ x, M.Nondegenerate (M.exteriorDerivative (alpha r)) x) :
    ∃ V : Set (ℝ × M.Point), IsOpen V ∧ A ×ˢ univ ⊆ V ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
        (fun q : ℝ × M.Point =>
          (⟨q.2, M.liouvilleVector (alpha q.1) q.2⟩ :
            TangentBundle 𝓘(ℝ, Model d) M.Point)) V := by
  let f := fun q : ℝ × M.Point =>
    (⟨q.2, M.liouvilleVector (alpha q.1) q.2⟩ :
      TangentBundle 𝓘(ℝ, Model d) M.Point)
  let S : Set (Set (ℝ × M.Point)) := {U | IsOpen U ∧
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞ f U}
  refine ⟨⋃₀ S, isOpen_sUnion (fun _ hU => hU.1), ?_, ?_⟩
  · intro p hp
    obtain ⟨U, hU, hpU, _, hfU⟩ :=
      M.exists_liouvilleVector_familyOn_neighborhood_at alpha hΩ halpha p
        (hcover hp) (hnd p.1 hp.1 p.2)
    exact mem_sUnion.mpr ⟨U, ⟨hU, hfU⟩, hpU⟩
  · intro p hp
    obtain ⟨U, hU, hpU⟩ := mem_sUnion.mp hp
    exact (hU.2.contMDiffAt (hU.1.mem_nhds hpU)).contMDiffWithinAt

end SmoothManifold

namespace IntrinsicSmoothBundle

/-- The source primitive in fixed coordinates is given only on the
retained base. Its raw real extension is ordinary smooth on a neighborhood
of that base times the manifold, with no off-base geometric requirements. -/
def IsSmoothSourcePrimitiveOnBase {d : ℕ}
    (Z : Parameter → CompleteLiouvilleManifold d) (N : SmoothManifold d)
    (B : Set Parameter) (R : ∀ s, s ∈ B → (Z s).manifold.SmoothEquiv N) : Prop :=
  ∃ (alpha : ℝ → N.Form 1) (Ω : Set (ℝ × N.Point)), IsOpen Ω ∧
    (Subtype.val '' B) ×ˢ univ ⊆ Ω ∧ N.IsSmoothFormFamilyOn alpha Ω ∧
    ∀ s (hs : s ∈ B), alpha s.val =
      N.pullback (Z s).manifold (R s hs).symm (Z s).primitive

/-- Ordinary target-valued source map germs whose map is defined only
at parameters in the retained base. -/
def HasSmoothTargetFamilyOnBase {a r : ℕ} {H M : Type*}
    [TopologicalSpace H] [TopologicalSpace M]
    (I : ModelWithCorners ℝ (Model a) H) [ChartedSpace H M]
    (N : SmoothManifold r) (B : Set Parameter)
    (v : ∀ s, s ∈ B → M → N.Point) : Prop :=
  ∀ e : OpenPartialHomeomorph M H, e ∈ atlas H M →
    ∀ s (_hs : s ∈ B), ∀ x ∈ e.source,
      ∃ U : TopologicalSpace.Opens (ℝ × Model a),
        (s.val, e.extend I x) ∈ U ∧ ∃ β : U → N.Point,
          ContMDiff 𝓘(ℝ, ℝ × Model a) 𝓘(ℝ, Model r) ∞ β ∧
          ∀ t (ht : t ∈ B), ∀ y ∈ e.source, ∀ h : (t.val, e.extend I y) ∈ U,
            β ⟨(t.val, e.extend I y), h⟩ = v t ht y

/-- Ordinary real finite-time germs, with the source flow itself defined
only on the retained base. Both signs and arbitrary finite times occur. -/
def HasRealSmoothFlowGermsOnBase {d : ℕ} (N : SmoothManifold d) (B : Set Parameter)
    (φ : ∀ s, s ∈ B → ℝ → N.Point → N.Point) : Prop :=
  ∀ s (_hs : s ∈ B), ∀ r (x : N.Point),
    ∃ U : Set (ℝ × (ℝ × N.Point)), IsOpen U ∧ (s.val, (r, x)) ∈ U ∧
      ∃ β : ℝ × (ℝ × N.Point) → N.Point,
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)))
          𝓘(ℝ, Model d) ∞ β U ∧
        ∀ t (ht : t ∈ B), ∀ a y, (t.val, (a, y)) ∈ U →
          β (t.val, (a, y)) = φ t ht a y

/-- Extending map values arbitrarily outside the base changes none of
its ordinary source chart germs. This does not extend source geometry. -/
theorem HasSmoothTargetFamilyOnBase.to_total {a r : ℕ} {H M : Type*}
    [TopologicalSpace H] [TopologicalSpace M]
    {I : ModelWithCorners ℝ (Model a) H} [ChartedSpace H M]
    {N : SmoothManifold r} {B : Set Parameter}
    {v : ∀ s, s ∈ B → M → N.Point} (hv : HasSmoothTargetFamilyOnBase I N B v)
    (w : Parameter → M → N.Point) (heq : ∀ s (hs : s ∈ B) x, w s x = v s hs x) :
    HasSmoothTargetFamilyOn I N B w := by
  intro e he s hs x hx
  obtain ⟨U, hpU, β, hβ, hβeq⟩ := hv e he s hs x hx
  refine ⟨U, hpU, β, hβ, ?_⟩
  intro t ht y hy h
  exact (hβeq t ht y hy h).trans (heq t ht y).symm

/-- Source primitive regularity on the retained base produces actual
finite-time flow germs. Symplecticity and the contraction equation are
proved from the actual slice sources, not added as regularity premises. -/
theorem completeFlowInCoordinates_realGermsOnBase_of_smooth_primitive
    {d : ℕ} (Z : Parameter → CompleteLiouvilleManifold d) (N : SmoothManifold d)
    (B : Set Parameter) (R : ∀ s, s ∈ B → (Z s).manifold.SmoothEquiv N)
    (hα : IsSmoothSourcePrimitiveOnBase Z N B R) :
    HasRealSmoothFlowGermsOnBase N B
      (fun s hs r y => R s hs ((Z s).completeFlow.flow r ((R s hs).symm y))) := by
  obtain ⟨alpha, Ω, hΩ, hcover, hαsmooth, hαeq⟩ := hα
  have hnd : ∀ r ∈ Subtype.val '' B, ∀ x,
      N.Nondegenerate (N.exteriorDerivative (alpha r)) x := by
    rintro r ⟨s, hs, rfl⟩ x
    rw [hαeq s hs]
    exact (Z s).nondegenerate_pullback_primitive N (R s hs).symm x
  obtain ⟨V, hV, hVcover, hW⟩ :=
    N.exists_liouvilleVector_familyOn_neighborhood alpha hΩ hαsmooth
      (Subtype.val '' B) hcover hnd
  let W := fun r => N.liouvilleVector (alpha r)
  have hWeq (s : Parameter) (hs : s ∈ B) (y : N.Point) :
      W s.val y = completeFieldInCoordinates (Z s) N (R s hs) y := by
    dsimp only [W]
    rw [hαeq s hs]
    exact N.liouvilleVector_eq _ y
      ((Z s).nondegenerate_pullback_primitive N (R s hs).symm y)
      ((Z s).liouvilleEquation_pullback_field N (R s hs).symm y)
  let ζ : Parameter → (x : N.Point) → N.Tangent x :=
    fun s => if hs : s ∈ B then completeFieldInCoordinates (Z s) N (R s hs)
      else fun _ => 0
  let Φ : Parameter → ℝ → N.Point → N.Point :=
    fun s r y => if hs : s ∈ B then R s hs ((Z s).completeFlow.flow r ((R s hs).symm y))
      else y
  intro s hs r x
  have hζ : ∀ v ∈ B, ContMDiff 𝓘(ℝ, Model d) (𝓘(ℝ, Model d)).tangent ∞
      (fun y => (⟨y, ζ v y⟩ : TangentBundle 𝓘(ℝ, Model d) N.Point)) := by
    intro v hv
    simpa only [ζ, dite_eq_left hv] using completeFieldInCoordinates_smooth (Z v) N (R v hv)
  have hself : ∀ v ∈ B, ∀ y, Φ v 0 y = y := by
    intro v hv y
    simp only [Φ, dite_eq_left hv, Flow.map_zero_apply, (R v hv).apply_symm_apply]
  have hcurve : ∀ v ∈ B, ∀ y, IsMIntegralCurve (fun a => Φ v a y) (ζ v) := by
    intro v hv y
    simpa only [Φ, ζ, dite_eq_left hv] using
      completeFlowInCoordinates_isMIntegralCurve (Z v) N (R v hv) y
  have hext : ∀ v ∈ B, ∀ y, (v.val, y) ∈ V → W v.val y = ζ v y := by
    intro v hv y _
    simpa only [ζ, dite_eq_left hv] using hWeq v hv y
  have horbit : ∀ a ∈ Icc (-(|r| + 1)) (|r| + 1), (s.val, Φ s a x) ∈ V := by
    intro a _
    exact hVcover ⟨⟨s, hs, rfl⟩, mem_univ _⟩
  obtain ⟨U, hU, hpU, β, hβ, heq⟩ :=
    CollarFlow.exists_parameterCompleteFlow_realGerm B ζ hζ Φ hself hcurve W hV hW
      hext s hs r x (|r| + 1) (by linarith) horbit
  refine ⟨U, hU, hpU, β, hβ, ?_⟩
  intro v hv a y hy
  simpa only [Φ, dite_eq_left hv] using heq v hv a y hy


/-- Arbitrary off-base values of the same finite-time map change none of
its real germs. Only map values are totalized; no source geometry is. -/
theorem HasRealSmoothFlowGermsOnBase.to_total {d : ℕ} {N : SmoothManifold d}
    {B : Set Parameter} {φ : ∀ s, s ∈ B → ℝ → N.Point → N.Point}
    (hφ : HasRealSmoothFlowGermsOnBase N B φ) (ψ : Parameter → ℝ → N.Point → N.Point)
    (heq : ∀ s (hs : s ∈ B) r y, ψ s r y = φ s hs r y) :
    HasRealSmoothFlowGermsOn N B ψ := by
  intro s hs r x
  obtain ⟨U, hU, hpU, β, hβ, hβeq⟩ := hφ s hs r x
  refine ⟨U, hU, hpU, β, hβ, ?_⟩
  intro t ht a y hy
  exact (hβeq t ht a y hy).trans (heq t ht a y).symm

variable {k d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {E : Parameter → Type*} [∀ s, TopologicalSpace (E s)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]
  {P : BundlePrimitiveData (k := k) (M := M) E}
  {L : OriginalBundleLiouvilleLaws P} {Z : Parameter → CompleteLiouvilleManifold d}
  {c : OriginalCompactChart (k := k) (M := M) (E := E)} {t : Parameter}

local instance localSourceMarkingProductCharts :
    ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ

namespace OriginalBundleCompletionMarkingData

/-- Ordinary compact inclusion and source primitive regularity on the
retained base produce real germs of the actual retained marking on every
native interior chart and the entire signed cylinder. The fixed source
coordinates are required only on that base. -/
theorem localEquiv_realGerms_of_source_inclusion_and_primitive_smooth_onBase
    (O : OriginalBundleCompletionMarkingData L Z) (F : LocalCompletionFamily P c t)
    (N : SmoothManifold d) (R : ∀ s, s ∈ F.base → (Z s).manifold.SmoothEquiv N)
    (hi : HasSmoothTargetFamilyOnBase (𝓡∂ (k + 1)) N F.base
      (fun s hs x => R s hs (chartValue c.val (O.compact s) s x)))
    (hα : IsSmoothSourcePrimitiveOnBase Z N F.base R) :
    (∀ s (_hs : s ∈ F.base) (u w : IntrinsicInterior.Point k M),
      w ∈ (chartAt (Model (k + 1)) u).source →
      ∃ U : Set (ℝ × Model (k + 1)), IsOpen U ∧
        (s.val, chartAt (Model (k + 1)) u w) ∈ U ∧
        ∃ β : ℝ × Model (k + 1) → N.Point,
          ContMDiffOn 𝓘(ℝ, ℝ × Model (k + 1)) 𝓘(ℝ, Model d) ∞ β U ∧
          ∀ v (hv : v ∈ F.base) z, z ∈ (chartAt (Model (k + 1)) u).source →
            (v.val, chartAt (Model (k + 1)) u z) ∈ U →
            β (v.val, chartAt (Model (k + 1)) u z) =
              ((O.localEquiv F v hv).trans (R v hv)) (interiorIn (F.native.patches v) z)) ∧
    (∀ s (_hs : s ∈ F.base) (u : IntrinsicBoundary.Point k M × ℝ)
      (p : Band F.native.width (IntrinsicBoundary.Point k M)),
      endBandCoordinates p ∈ (chartAt (Model k × ℝ) u).source →
      ∃ U : Set (ℝ × (Model k × ℝ)), IsOpen U ∧
        (s.val, chartAt (Model k × ℝ) u (endBandCoordinates p)) ∈ U ∧
        ∃ β : ℝ × (Model k × ℝ) → N.Point,
          ContMDiffOn 𝓘(ℝ, ℝ × (Model k × ℝ)) 𝓘(ℝ, Model d) ∞ β U ∧
          ∀ v (hv : v ∈ F.base) (q : Band F.native.width (IntrinsicBoundary.Point k M)),
            endBandCoordinates q ∈ (chartAt (Model k × ℝ) u).source →
            (v.val, chartAt (Model k × ℝ) u (endBandCoordinates q)) ∈ U →
            β (v.val, chartAt (Model k × ℝ) u (endBandCoordinates q)) =
              ((O.localEquiv F v hv).trans (R v hv)) (cylinder (F.native.patches v) q)) := by
  let η : Parameter → M → N.Point := fun s x =>
    if hs : s ∈ F.base then R s hs (chartValue c.val (O.compact s) s x)
      else R t F.base_mem (chartValue c.val (O.compact t) t x)
  have hη : HasSmoothTargetFamilyOn (𝓡∂ (k + 1)) N F.base η :=
    hi.to_total η (by intro s hs x; simp only [η, dite_eq_left hs])
  let Φ : Parameter → ℝ → N.Point → N.Point := fun s r y =>
    if hs : s ∈ F.base then R s hs ((Z s).completeFlow.flow r ((R s hs).symm y))
      else y
  have hΦ : HasRealSmoothFlowGermsOn N F.base Φ :=
    (completeFlowInCoordinates_realGermsOnBase_of_smooth_primitive Z N F.base R hα).to_total
      Φ (by intro s hs r y; simp only [Φ, dite_eq_left hs])
  constructor
  · intro s hs u w hw
    obtain ⟨U, hU, hpU, β, hβ, heq⟩ := hη.rawInteriorGerm N s hs u w hw
    refine ⟨U, hU, hpU, β, hβ, ?_⟩
    intro v hv z hz hzU
    rw [heq v hv z hz hzU]
    simp only [η, dite_eq_left hv]
    change R v hv (chartValue c.val (O.compact v) v z.val) =
      R v hv (O.localEquiv F v hv (original (F.native.patches v) z.val))
    rw [O.localEquiv_native]
  · intro s hs u p hp
    obtain ⟨U, hU, hpU, β, hβ, heq⟩ :=
      hη.rawBoundaryFlowGerm N Φ hΦ s hs u (endBandCoordinates p) hp
    refine ⟨U, hU, hpU, β, hβ, ?_⟩
    intro v hv q hq hqU
    rw [heq v hv (endBandCoordinates q) hq hqU]
    simp only [Φ, η, dite_eq_left hv]
    change R v hv ((Z v).completeFlow.flow (-q.val.1)
      ((R v hv).symm (R v hv (chartValue c.val (O.compact v) v q.val.2.val)))) =
      R v hv (O.localEquiv F v hv (cylinder (F.native.patches v) q))
    rw [(R v hv).symm_apply_apply]
    have hq' : (F.sliceCompletion L v).endMap (q.val.2, -q.val.1) =
        cylinder (F.native.patches v) q :=
      F.sliceCompletion_end_cylinder L v q.val.2 q.val.1 q.property.1
    rw [← hq', O.localEquiv_end]

end OriginalBundleCompletionMarkingData

end IntrinsicSmoothBundle
end FsFltz.Geometry
