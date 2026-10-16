import FsFltz.Geometry.IntrinsicNativeCompletionFamilyVerticalExterior
import FsFltz.Geometry.IntrinsicNativeCompletionFamilyCovectorGerms

/-!
# Real open coefficients of the original spatial two-form

Source: `geoemtric-part-fsf.tex`, conventions lines 119–122; `def:chain`,
lines 163–169; `sec:lean`, lines 788–814. Real parameter map extensions
and the spatial exterior derivative of the real reference primitive family
produce full two-form coefficients on the original completed-family patches.
These coefficients include parameter tangent directions. The two-form is the
pullback of the spatial derivative, not the total exterior derivative of a
parameterized primitive. The endpoint extension is across genuine real open
neighborhoods, not only smoothness in the closed interval model.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry

/-- Smooth two-forms can be pulled back by smoothly varying linear maps.
The proof curries both arguments and alternatizes back, retaining the full
two-form rather than only scalar evaluation on a chosen pair of vectors. -/
theorem contDiffOn_twoForm_compContinuousLinearMap
    {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set X} {η : X → F [⋀^Fin 2]→L[ℝ] ℝ} {B : X → E →L[ℝ] F}
    (hη : ContDiffOn ℝ ∞ η U) (hB : ContDiffOn ℝ ∞ B U) :
    ContDiffOn ℝ ∞ (fun p => (η p).compContinuousLinearMap (B p)) U := by
  let eF := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := F) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  let eE := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  let cF := (ContinuousAlternatingMap.curryLeftLI
    (𝕜 := ℝ) (E := F) (F := ℝ) (n := 1)).toContinuousLinearMap
  have hc := (ContinuousLinearMap.contDiff (𝕜 := ℝ)
    (E := F [⋀^Fin 2]→L[ℝ] ℝ) (F := F →L[ℝ] F [⋀^Fin 1]→L[ℝ] ℝ) cF).comp_contDiffOn hη
  have hLF : ContDiffOn ℝ ∞ (fun _ : X => eF.symm.toContinuousLinearMap) U :=
    contDiffOn_const
  have hd := hLF.clm_comp (hc.clm_comp hB)
  have hf := (LinearIsometryEquiv.contDiff (𝕜 := ℝ)
    (E := E →L[ℝ] F →L[ℝ] ℝ) (F := F →L[ℝ] E →L[ℝ] ℝ)
    (ContinuousLinearMap.flipₗᵢ ℝ E F ℝ)).comp_contDiffOn hd
  have hb := (LinearIsometryEquiv.contDiff (𝕜 := ℝ)
    (E := E →L[ℝ] E →L[ℝ] ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ)
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ)).comp_contDiffOn
    (hf.clm_comp hB)
  have hLE : ContDiffOn ℝ ∞ (fun _ : X => eE.toContinuousLinearMap) U := contDiffOn_const
  have ha := hLE.clm_comp hb
  have heq : (fun p => eE.toContinuousLinearMap ∘L
      (((eF.symm.toContinuousLinearMap ∘L (cF (η p) ∘L B p)).flip ∘L B p).flip)) =
      (fun p => ((η p).compContinuousLinearMap (B p)).curryLeft) := by
    funext p
    ext v vs
    change η p (Matrix.vecCons (B p v) (fun _ : Fin 1 => B p (vs 0))) =
      η p (fun j => B p (Matrix.vecCons v vs j))
    congr 1
    funext j
    fin_cases j <;> rfl
  change ContDiffOn ℝ ∞ (fun p => eE.toContinuousLinearMap ∘L
    (((eF.symm.toContinuousLinearMap ∘L (cF (η p) ∘L B p)).flip ∘L B p).flip)) U at ha
  rw [heq] at ha
  have hs := ((ContinuousLinearMap.contDiff (𝕜 := ℝ)
    (E := E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ) (F := E [⋀^Fin 2]→L[ℝ] ℝ)
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ (n := 1))).comp_contDiffOn ha).const_smul (1 / 2 : ℝ)
  apply hs.congr
  intro p _
  simp only [Function.comp_apply, ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply,
    ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  norm_num

end FsFltz.Geometry

namespace FsFltz.Geometry.SmoothManifold

/-- Coefficients of an interval-product two-form in natural real parameter
and spatial chart coordinates. The time argument is a full tangent direction. -/
def intervalTwoFormInChart {d : ℕ} (M : SmoothManifold d)
    (Ω : (p : Parameter × M.Point) → TangentSpace ((𝓡∂ 1).prod 𝓘(ℝ, Model d)) p
      [⋀^Fin 2]→L[ℝ] ℝ) (a : M.Point) (t : Parameter) (y : Model d) :
    (ℝ × Model d) [⋀^Fin 2]→L[ℝ] ℝ :=
  (Ω (t, (chartAt (Model d) a).symm y)).compContinuousLinearMap
    (((ContinuousLinearMap.id ℝ ℝ).smulRight (1 : TangentSpace (𝓡∂ 1) t)).prodMap
      (M.inverseChartTangentMap a y))

/-- The same coefficients for an actual real parameter map and form family. -/
def realPullbackTwoFormInChart {d e : ℕ} (M : SmoothManifold d) (N : SmoothManifold e)
    (f : ℝ → M.Point → N.Point) (α : ℝ → N.Form 2) (a : M.Point)
    (p : ℝ × Model d) : (ℝ × Model d) [⋀^Fin 2]→L[ℝ] ℝ :=
  (α p.1 (f p.1 ((chartAt (Model d) a).symm p.2))).compContinuousLinearMap
    ((mfderiv ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e)
      (fun q : ℝ × M.Point => f q.1 q.2) (p.1, (chartAt (Model d) a).symm p.2)).comp
        ((ContinuousLinearMap.id ℝ ℝ).prodMap (M.inverseChartTangentMap a p.2)))

/-- An actual real parameter map pulls a real smooth form family to full
two-form coefficients on open neighborhoods of all interval chart points. -/
theorem smoothNearInterval_realPullbackTwoFormInChart {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e)
    (f : ℝ → M.Point → N.Point)
    (hf : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞
      (fun q : ℝ × M.Point => f q.1 q.2))
    (α : ℝ → N.Form 2) (hα : N.IsSmoothFormFamily α) (a : M.Point) :
    SmoothNearInterval (chartAt (Model d) a).target
      (M.realPullbackTwoFormInChart N f α a) := by
  apply smoothNearInterval_of_local
  rintro ⟨t, y⟩ ⟨ht, hy⟩
  let c := chartAt (Model d) a
  let x := f t (c.symm y)
  let b := chartAt (Model e) x
  let k : ℝ × Model d → N.Point := fun p => f p.1 (c.symm p.2)
  have hk : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞ k
      (univ ×ˢ c.target) :=
    hf.comp_contMDiffOn (contMDiffOn_fst.prodMk
      ((contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d)) (x := a)).comp
        contMDiffOn_snd (fun _ hp => hp.2)))
  let S := (univ ×ˢ c.target) ∩ k ⁻¹' b.source
  have hS : IsOpen S := hk.continuousOn.isOpen_inter_preimage
    (isOpen_univ.prod c.open_target) b.open_source
  have hpS : (t, y) ∈ S := ⟨⟨mem_univ _, hy⟩, mem_chart_source _ _⟩
  let g : ℝ × Model d → Model e := fun p => b (k p)
  have hgm : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞ g S :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model e)) (x := x)).comp
      (hk.mono inter_subset_left) inter_subset_right
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hgm
  have hg : ContDiffOn ℝ ∞ g S := hgm.contDiffOn
  obtain ⟨A, hA, hcover, hcoeff⟩ := hα x
  let q : ℝ × Model d → ℝ × Model e := fun p => (p.1, g p)
  have hq : ContDiffOn ℝ ∞ q S := contDiffOn_fst.prodMk hg
  let U := S ∩ q ⁻¹' A
  have hU : IsOpen U := hq.continuousOn.isOpen_inter_preimage hS hA
  have hpU : (t, y) ∈ U := ⟨hpS, hcover ⟨ht, b.map_source (mem_chart_source _ _)⟩⟩
  have hc : ContDiffOn ℝ ∞ (fun p => N.formInChart x (α p.1) (g p)) U :=
    hcoeff.comp (hq.mono inter_subset_left) inter_subset_right
  have hB : ContDiffOn ℝ ∞ (fderiv ℝ g) U :=
    (hg.fderiv_of_isOpen (m := ∞) hS (by simp)).mono inter_subset_left
  have hforms := contDiffOn_twoForm_compContinuousLinearMap hc hB
  refine ⟨U, hU, hpU, hforms.congr ?_⟩
  intro p hp
  have hpct : p.2 ∈ c.target := hp.1.1.2
  have hpk : k p ∈ b.source := hp.1.2
  have hcs := (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d)) (x := a) (n := ∞)).contMDiffAt
    (c.open_target.mem_nhds hpct)
  have hq₀ : ContMDiffAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
      (fun z : ℝ × Model d => (z.1, c.symm z.2)) p :=
    contMDiffAt_fst.prodMk (hcs.comp p contMDiffAt_snd)
  have hdk := mfderiv_comp p (hf.mdifferentiableAt (by simp))
    (hq₀.mdifferentiableAt (by simp))
  have hdb := mfderiv_comp p
    (((contMDiffOn_chart (I := 𝓘(ℝ, Model e)) (x := x) (n := ∞)).contMDiffAt
      (b.open_source.mem_nhds hpk)).mdifferentiableAt (by simp))
    ((hk.contMDiffAt ((isOpen_univ.prod c.open_target).mem_nhds hp.1.1)).mdifferentiableAt
      (by simp))
  have hdg : mfderiv ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) g p =
      fderiv ℝ g p := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact mfderiv_eq_fderiv
  have hdiag : mfderiv ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      (fun z : ℝ × Model d => (z.1, c.symm z.2)) p =
        (ContinuousLinearMap.id ℝ ℝ).prodMap (M.inverseChartTangentMap a p.2) := by
    change mfderiv _ _ (Prod.map id c.symm) p = _
    rw [mfderiv_prodMap mdifferentiableAt_id (hcs.mdifferentiableAt (by simp)), mfderiv_id]
    rfl
  rw [hdiag] at hdk
  have hinv := (mdifferentiable_chart (I := 𝓘(ℝ, Model e)) x).symm_comp_deriv hpk
  symm
  ext vs
  dsimp only [formInChart, realPullbackTwoFormInChart]
  rw [b.left_inv hpk]
  change (α p.1 (k p)) (fun j =>
      mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model e) b.symm (b (k p))
        (fderiv ℝ g p (vs j))) = _
  erw [← hdg, hdb, hdk]
  change (α p.1 (k p)) (fun j =>
    ((mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model e) b.symm (b (k p))).comp
      (mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model e) b (k p)))
      (mfderiv ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e)
        (fun q : ℝ × M.Point => f q.1 q.2) (p.1, c.symm p.2)
          (((ContinuousLinearMap.id ℝ ℝ).prodMap (M.inverseChartTangentMap a p.2))
            (vs j)))) = _
  erw [hinv]
  rfl

/-- Real full pullback coefficients restrict to the natural coefficients of
the native interval two-form, including all time and spatial directions. -/
theorem intervalTwoFormInChart_nativeTotalTwoForm_realMap {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e)
    (f : ℝ → M.Point → N.Point)
    (hf : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞
      (fun q : ℝ × M.Point => f q.1 q.2))
    (α : Parameter → N.Form 2) (β : ℝ → N.Form 2)
    (heq : ∀ t, β t.val = α t) (a : M.Point) (t : Parameter) (y : Model d) :
    M.intervalTwoFormInChart
      (nativeTotalTwoForm ((𝓡∂ 1).prod 𝓘(ℝ, Model d)) N Prod.fst
        (fun p : Parameter × M.Point => f p.1.val p.2) α) a t y =
      M.realPullbackTwoFormInChart N f β a (t.val, y) := by
  ext vs
  dsimp only [intervalTwoFormInChart, nativeTotalTwoForm, realPullbackTwoFormInChart]
  rw [heq t]
  change (α t (f t.val ((chartAt (Model d) a).symm y)))
      (fun j => mfderiv ((𝓡∂ 1).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e)
        (fun p : Parameter × M.Point => f p.1.val p.2)
        (t, (chartAt (Model d) a).symm y)
        ((vs j).1 • (1 : TangentSpace (𝓡∂ 1) t),
          M.inverseChartTangentMap a y (vs j).2)) =
    (α t (f t.val ((chartAt (Model d) a).symm y)))
      (fun j => mfderiv ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e)
        (fun p : ℝ × M.Point => f p.1 p.2)
        (t.val, (chartAt (Model d) a).symm y)
        ((vs j).1, M.inverseChartTangentMap a y (vs j).2))
  congr 1
  funext j
  exact M.mfderiv_intervalRealMap N f hf _ (vs j).1 _

/-- Full interval two-form coefficients have one real smooth extension in
every spatial chart, agreeing on the indicated open spatial patch. -/
def HasRealIntervalTwoFormCoefficientsOn {d : ℕ} (M : SmoothManifold d)
    (Ω : (p : Parameter × M.Point) → TangentSpace ((𝓡∂ 1).prod 𝓘(ℝ, Model d)) p
      [⋀^Fin 2]→L[ℝ] ℝ) (A : Set M.Point) : Prop :=
  IsOpen A ∧ ∀ a, ∃ B : ℝ × Model d → (ℝ × Model d) [⋀^Fin 2]→L[ℝ] ℝ,
    SmoothNearInterval (chartAt (Model d) a).target B ∧
    ∀ (t : Parameter) y, y ∈ (chartAt (Model d) a).target →
      (chartAt (Model d) a).symm y ∈ A → M.intervalTwoFormInChart Ω a t y = B (t.val, y)

/-- A real map and the existing real primitive coefficient extensions
produce the full coefficient germ of any literally matching two-form. -/
theorem hasRealIntervalTwoFormCoefficientsOn_of_realMap {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e)
    (f : ℝ → M.Point → N.Point)
    (hf : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞
      (fun q : ℝ × M.Point => f q.1 q.2))
    (α : Parameter → N.Form 2) (hα : N.IsSmoothIntervalFormFamily α)
    (Ω : (p : Parameter × M.Point) → TangentSpace ((𝓡∂ 1).prod 𝓘(ℝ, Model d)) p
      [⋀^Fin 2]→L[ℝ] ℝ)
    (A : Set M.Point) (hA : IsOpen A)
    (heq : ∀ p : Parameter × M.Point, p.2 ∈ A → Ω p =
      nativeTotalTwoForm ((𝓡∂ 1).prod 𝓘(ℝ, Model d)) N Prod.fst
        (fun p : Parameter × M.Point => f p.1.val p.2) α p) :
    M.HasRealIntervalTwoFormCoefficientsOn Ω A := by
  obtain ⟨β, hβ, heβ⟩ := hα
  refine ⟨hA, fun a => ⟨M.realPullbackTwoFormInChart N f β a,
    M.smoothNearInterval_realPullbackTwoFormInChart N f hf β hβ a, ?_⟩⟩
  intro t y _ hy
  dsimp only [intervalTwoFormInChart]
  rw [heq _ hy]
  exact M.intervalTwoFormInChart_nativeTotalTwoForm_realMap N f hf α β heβ a t y

end FsFltz.Geometry.SmoothManifold

namespace FsFltz.Geometry

section TwoFormComposition
variable {E H X F G Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G] [TopologicalSpace Y]
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F G)
  [ChartedSpace H X] [ChartedSpace G Y]

/-- The full derivative of the actual patch pulls back the canonical total
two-form. This identity retains any parameter component of the two-form. -/
theorem nativeTotalTwoForm_comp {d : ℕ} (N : SmoothManifold d)
    (p : X → Parameter) (q : X → N.Point) (α : Parameter → N.Form 2)
    (hq : ContMDiff I 𝓘(ℝ, Model d) ∞ q)
    (j : Y → X) (hj : ContMDiff J I ∞ j) (y : Y) :
    (nativeTotalTwoForm I N p q α (j y)).compContinuousLinearMap (mfderiv J I j y) =
      nativeTotalTwoForm J N (p ∘ j) (q ∘ j) α y := by
  have hd := mfderiv_comp y (hq.mdifferentiableAt (by simp))
    (hj.mdifferentiableAt (by simp))
  ext vs
  dsimp only [nativeTotalTwoForm, Function.comp_def]
  change (α (p (j y)) (q (j y))) (fun k =>
      mfderiv I 𝓘(ℝ, Model d) q (j y) (mfderiv J I j y (vs k))) =
    (α (p (j y)) (q (j y))) (fun k =>
      mfderiv J 𝓘(ℝ, Model d) (q ∘ j) y (vs k))
  rw [hd]
  rfl

end TwoFormComposition
end FsFltz.Geometry


namespace FsFltz.Geometry.PairDeformation
open SmoothManifold IntrinsicCompletionGluing IntrinsicLiouville

variable {k n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- The same original total two-form has actual real open full coefficients
in its full-cylinder patch on a uniform seam/outward strip. Its time
component is obtained from the full real cylinder differential. -/
theorem exists_ambientNativeCylinderTwoForm_coefficients
    (Q : PairDeformation n) (hdim : k + 1 = 2 * n)
    (α : Parameter → Form k M 1)
    (e : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
      (Q.pair t).ambientDomain.domain.Point ∞)
    (hp : ∀ t x, ((Q.pair t).ambientDomain.liouville.primitive (e t x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (e t y).val) x) = α t x)
    (hc : ∀ t, HasNativeCoordinateExtensions (k := k)
      (Q.pair t).ambientDomain.domain.extension (fun x => (e t x).val))
    (b : ∀ t, (IntrinsicBoundary.smoothManifold k M).SmoothEquiv
      (Q.pair t).ambientDomain.domain.boundary)
    (hb : ∀ t x, (Q.pair t).ambientDomain.domain.boundaryInclusion.map (b t x) = (e t x.val).val)
    (hsquare : ∀ t x, (Q.ambientPresentation t).boundaryEquiv (b parameterZero x) = b t x)
    {δ : ℝ} (hδ : 0 < δ) (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
    (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
      (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
    (hzero : ∀ t x, C t (0, x) = x.val)
    (hjoint : IsOpenEmbedding (totalCollar
      (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
    (hmix : HasRealMixedGerms (δ := δ) C)
    (hode : ∀ t x, IsMIntegralCurveOn (fun s => C t (s, x))
      (fun z => -liouvilleVector (α t) (exteriorDerivative (α t)) z) (Ico 0 δ))
    (q : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) →
      Q.source.ambientCompletion.ambient.manifold.Point)
    (hq : letI := totalFamilyChartedSpace hδ C hzero hjoint
      ContMDiff (familyModel (k + 1)) 𝓘(ℝ, Model (2 * n)) ∞ q)
    (hqend : ∀ (t : Parameter) (p : Band δ (IntrinsicBoundary.Point k M)),
      q (totalCylinder (fun t p => C t p.val) (t, p)) =
        (Q.ambientCompletionPresentation t).prescribedEndMap (b parameterZero p.val.2, -p.val.1)) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    letI := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) δ
    let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
    let Ξ := nativeTotalTwoForm (familyModel (k + 1))
      Q.source.ambientCompletion.ambient.manifold (parameter c) q
      (fun t => Q.source.ambientCompletion.ambient.manifold.exteriorDerivative (Q.completedPrimitive t))
    ∃ a : ℝ, a < 0 ∧
      (bandManifold δ (IntrinsicBoundary.smoothManifold k M)).HasRealIntervalTwoFormCoefficientsOn
        (fun p => (Ξ (totalCylinder c p)).compContinuousLinearMap
          (mfderiv (familyModel (k + 1)) (familyModel (k + 1)) (totalCylinder c) p))
        {p | a < -p.val.1} := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) δ
  let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
  let P := bandManifold δ (IntrinsicBoundary.smoothManifold k M)
  let N := Q.source.ambientCompletion.ambient.manifold
  let η := fun t => N.exteriorDerivative (Q.completedPrimitive t)
  obtain ⟨a, ha, β, hβ, heβ, _, _⟩ :=
    Q.exists_ambientNativeCylinderFamily_extension hdim α e hp hc b hb hsquare C hode hzero
  let f : ℝ → P.Point → N.Point := fun t p => β t (p.val.2, -p.val.1)
  have hf : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
      𝓘(ℝ, Model (2 * n)) ∞ (fun p : ℝ × P.Point => f p.1 p.2) :=
    hβ.comp (contMDiff_fst.prodMk
      ((contMDiff_snd.comp ((contMDiff_band_val δ).comp contMDiff_snd)).prodMk
        (contMDiff_fst.comp ((contMDiff_band_val δ).comp contMDiff_snd)).neg))
  have hA : IsOpen {p : P.Point | a < -p.val.1} :=
    isOpen_lt continuous_const (continuous_fst.comp continuous_subtype_val).neg
  refine ⟨a, ha, P.hasRealIntervalTwoFormCoefficientsOn_of_realMap N f hf
    η Q.completedAmbientPrimitive_smooth.exteriorDerivative _ _ hA ?_⟩
  intro p hpA
  rw [nativeTotalTwoForm_comp (familyModel (k + 1)) (familyModel (k + 1))
    N (parameter c) q
      (fun t => Q.source.ambientCompletion.ambient.manifold.exteriorDerivative (Q.completedPrimitive t)) hq (totalCylinder c)
    (contMDiff_totalCylinder hδ C hboundary hzero hjoint hmix) p]
  have hparam : parameter c ∘ totalCylinder c = Prod.fst := by
    funext z
    exact parameter_totalCylinder c z
  rw [hparam]
  have he : q ∘ totalCylinder c =ᶠ[𝓝 p]
      (fun z : Parameter × P.Point => f z.1.val z.2) := by
    have hn : ∀ᶠ z : Parameter × P.Point in 𝓝 p, z.2 ∈ {p : P.Point | a < -p.val.1} :=
      continuous_snd.continuousAt.preimage_mem_nhds (hA.mem_nhds hpA)
    filter_upwards [hn] with z hz
    exact (hqend z.1 z.2).trans (heβ z.1 z.2.val.2 (-z.2.val.1) hz).symm
  have hvalue := he.eq_of_nhds
  have hderiv := he.mfderiv_eq (I := familyModel (k + 1)) (I' := 𝓘(ℝ, Model (2 * n)))
  have hd : mfderiv (familyModel (k + 1)) 𝓘(ℝ, Model (2 * n)) (q ∘ totalCylinder c) p =
      mfderiv (familyModel (k + 1)) 𝓘(ℝ, Model (2 * n))
        (fun z : Parameter × P.Point => f z.1.val z.2) p := by
    ext v
    exact congrArg (fun L : TangentSpace (familyModel (k + 1)) p →L[ℝ] Model (2 * n) => L v)
      hderiv
  change q (totalCylinder c p) = f p.1.val p.2 at hvalue
  ext vs
  dsimp only [nativeTotalTwoForm, Function.comp_def]
  erw [hvalue, hd]

/-- The real native deformation produces full real open two-form
coefficients on the whole original native interior, for the same total
two-form and the actual interior-patch differential. -/
theorem ambientNativeInteriorTwoForm_coefficients
    (Q : PairDeformation n)
    (e : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
      (Q.pair t).ambientDomain.domain.Point ∞)
    (R : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
    (hR : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) R)
    (hsquareA : ∀ t x, (Q.ambientPresentation t).extensionEquiv
      (e parameterZero (R t.val x)).val = (e t x).val)
    {δ : ℝ} (hδ : 0 < δ) (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
    (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
      (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
    (hzero : ∀ t x, C t (0, x) = x.val)
    (hjoint : IsOpenEmbedding (totalCollar
      (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
    (hmix : HasRealMixedGerms (δ := δ) C)
    (q : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) →
      Q.source.ambientCompletion.ambient.manifold.Point)
    (hq : letI := totalFamilyChartedSpace hδ C hzero hjoint
      ContMDiff (familyModel (k + 1)) 𝓘(ℝ, Model (2 * n)) ∞ q)
    (hqnative : ∀ t x,
      q (original (totalCollar (fun t p => C t p.val)) (t, x)) =
        Q.ambientNativeReferenceMap e t x) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
    let Ξ := nativeTotalTwoForm (familyModel (k + 1))
      Q.source.ambientCompletion.ambient.manifold (parameter c) q
      (fun t => Q.source.ambientCompletion.ambient.manifold.exteriorDerivative (Q.completedPrimitive t))
    (IntrinsicInterior.smoothManifold k M).HasRealIntervalTwoFormCoefficientsOn
      (fun p => (Ξ (totalInterior c p)).compContinuousLinearMap
        (mfderiv (familyModel (k + 1)) (familyModel (k + 1)) (totalInterior c) p)) univ := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
  let P := IntrinsicInterior.smoothManifold k M
  let N := Q.source.ambientCompletion.ambient.manifold
  let η := fun t => N.exteriorDerivative (Q.completedPrimitive t)
  let f₀ : M → N.Point := fun x => Q.source.ambientCompletion.inclusion.map (e parameterZero x).val
  have hf₀ : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) ∞ f₀ :=
    Q.source.ambientCompletion.inclusion.map.contMDiff.comp
      (Q.source.ambientDomain.domain.contMDiff_subtype_val.comp (e parameterZero).contMDiff)
  let f : ℝ → P.Point → N.Point := fun t x => f₀ (R t x.val)
  have hf : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
      𝓘(ℝ, Model (2 * n)) ∞ (fun p : ℝ × P.Point => f p.1 p.2) :=
    hf₀.comp (hR.1.comp (contMDiff_id.prodMap IntrinsicInterior.contMDiff_val))
  apply P.hasRealIntervalTwoFormCoefficientsOn_of_realMap N f hf
    η Q.completedAmbientPrimitive_smooth.exteriorDerivative _ univ isOpen_univ
  intro p _
  rw [nativeTotalTwoForm_comp (familyModel (k + 1)) (familyModel (k + 1))
    N (parameter c) q
      (fun t => Q.source.ambientCompletion.ambient.manifold.exteriorDerivative (Q.completedPrimitive t)) hq (totalInterior c)
    (contMDiff_totalInterior hδ C hboundary hzero hjoint hmix) p]
  have hparam : parameter c ∘ totalInterior c = Prod.fst := by
    funext z
    rfl
  have he : q ∘ totalInterior c = (fun p : Parameter × P.Point => f p.1.val p.2) := by
    funext p
    exact (hqnative p.1 p.2.val).trans
      (Q.ambientNativeReferenceMap_eq_compact e R hsquareA p.1 p.2.val)
  rw [hparam, he]

end FsFltz.Geometry.PairDeformation
