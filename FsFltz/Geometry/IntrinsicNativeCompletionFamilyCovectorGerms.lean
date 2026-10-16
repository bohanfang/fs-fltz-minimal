import FsFltz.Geometry.IntrinsicNativeCompletionFamilyVertical
import FsFltz.Geometry.FamilyPullback

/-!
# Real open coefficients of the original completion covector

Source: `geoemtric-part-fsf.tex`, differential-geometric conventions,
lines 119–122; `def:chain`, lines 163–169; and `sec:lean`, lines 788–814.
Real cylinder maps and real coefficient extensions of the reference primitive
produce coefficients of the full total covector, including its parameter
component. The equalities use the actual original interior and cylinder
differentials. Exterior-form and field endpoint germs remain separate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.SmoothManifold

/-- Coefficients of an interval-product covector in natural real parameter
and spatial chart coordinates. The time argument is a full tangent direction. -/
def intervalCovectorInChart {d : ℕ} (M : SmoothManifold d)
    (Ω : (p : Parameter × M.Point) → TangentSpace ((𝓡∂ 1).prod 𝓘(ℝ, Model d)) p
      [⋀^Fin 1]→L[ℝ] ℝ) (a : M.Point) (t : Parameter) (y : Model d) :
    (ℝ × Model d) [⋀^Fin 1]→L[ℝ] ℝ :=
  (Ω (t, (chartAt (Model d) a).symm y)).compContinuousLinearMap
    (((ContinuousLinearMap.id ℝ ℝ).smulRight (1 : TangentSpace (𝓡∂ 1) t)).prodMap
      (M.inverseChartTangentMap a y))

/-- The same coefficients for an actual real parameter map and form family. -/
def realPullbackCovectorInChart {d e : ℕ} (M : SmoothManifold d) (N : SmoothManifold e)
    (f : ℝ → M.Point → N.Point) (α : ℝ → N.Form 1) (a : M.Point)
    (p : ℝ × Model d) : (ℝ × Model d) [⋀^Fin 1]→L[ℝ] ℝ :=
  (α p.1 (f p.1 ((chartAt (Model d) a).symm p.2))).compContinuousLinearMap
    ((mfderiv ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e)
      (fun q : ℝ × M.Point => f q.1 q.2) (p.1, (chartAt (Model d) a).symm p.2)).comp
        ((ContinuousLinearMap.id ℝ ℝ).prodMap (M.inverseChartTangentMap a p.2)))

/-- The interval-to-real product inclusion sends the canonical time tangent
to the real time tangent, also at zero and one. -/
theorem mfderiv_intervalVal_prod {d : ℕ} (M : SmoothManifold d)
    (p : Parameter × M.Point) (r : ℝ) (v : Model d) :
    mfderiv ((𝓡∂ 1).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      (fun q : Parameter × M.Point => (q.1.val, q.2)) p
        (r • (1 : TangentSpace (𝓡∂ 1) p.1), v) = (r, v) := by
  change mfderiv ((𝓡∂ 1).prod 𝓘(ℝ, Model d))
    ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
    (Prod.map (Subtype.val : Parameter → ℝ) (id : M.Point → M.Point)) p
    (r • (1 : TangentSpace (𝓡∂ 1) p.1), v) = _
  rw [mfderiv_prodMap ((contMDiff_subtypeVal_Icc (n := ∞)).mdifferentiableAt (by simp))
    mdifferentiableAt_id, mfderiv_id]
  apply Prod.ext
  · change mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) Subtype.val p.1
      (r • (1 : TangentSpace (𝓡∂ 1) p.1)) = r
    rw [map_smul, mfderiv_subtypeVal_Icc_one, smul_eq_mul, mul_one]
  · rfl

/-- Every native interval tangent is represented by the canonical real
time direction. Thus natural time coefficients cover the whole time fiber. -/
theorem canonicalTimeTangent_decompose (t : Parameter) (v : TangentSpace (𝓡∂ 1) t) :
    (show ℝ from mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : Parameter → ℝ) t v) •
      (1 : TangentSpace (𝓡∂ 1) t) = v := by
  apply (isImmersionOfComplement_subtypeVal_Icc (x := (0 : ℝ)) (y := 1)
    (n := ∞)).injective_mfderiv (by simp) t
  rw [map_smul, mfderiv_subtypeVal_Icc_one, smul_eq_mul, mul_one]

/-- Restricting an actual real parameter map leaves its full differential
unchanged in the natural parameter coordinates. -/
theorem mfderiv_intervalRealMap {d e : ℕ} (M : SmoothManifold d)
    (N : SmoothManifold e) (f : ℝ → M.Point → N.Point)
    (hf : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞
      (fun q : ℝ × M.Point => f q.1 q.2)) (p : Parameter × M.Point)
    (r : ℝ) (v : Model d) :
    mfderiv ((𝓡∂ 1).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e)
      (fun q : Parameter × M.Point => f q.1.val q.2) p
        (r • (1 : TangentSpace (𝓡∂ 1) p.1), v) =
    mfderiv ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e)
      (fun q : ℝ × M.Point => f q.1 q.2) (p.1.val, p.2) (r, v) := by
  have hinc : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
      (fun q : Parameter × M.Point => (q.1.val, q.2)) :=
    contMDiff_subtypeVal_Icc.prodMap contMDiff_id
  have h := mfderiv_comp p (hf.mdifferentiableAt (by simp))
    (hinc.mdifferentiableAt (by simp))
  change mfderiv _ _ ((fun q : ℝ × M.Point => f q.1 q.2) ∘
    (fun q : Parameter × M.Point => (q.1.val, q.2))) p _ = _
  rw [h]
  erw [ContinuousLinearMap.comp_apply, M.mfderiv_intervalVal_prod]

/-- An actual real parameter map pulls a real smooth form family to full
covector coefficients on open neighborhoods of all interval chart points. -/
theorem smoothNearInterval_realPullbackCovectorInChart {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e)
    (f : ℝ → M.Point → N.Point)
    (hf : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞
      (fun q : ℝ × M.Point => f q.1 q.2))
    (α : ℝ → N.Form 1) (hα : N.IsSmoothFormFamily α) (a : M.Point) :
    SmoothNearInterval (chartAt (Model d) a).target
      (M.realPullbackCovectorInChart N f α a) := by
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
  let eF := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := Model e) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  let eE := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := ℝ × Model d) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  have hs := eE.contDiff.comp_contDiffOn
    ((eF.symm.contDiff.comp_contDiffOn hc).clm_comp hB)
  have hforms : ContDiffOn ℝ ∞ (fun p =>
      (N.formInChart x (α p.1) (g p)).compContinuousLinearMap (fderiv ℝ g p)) U := by
    convert hs using 1
    ext p vs
    change (N.formInChart x (α p.1) (g p)) (fun i => fderiv ℝ g p (vs i)) =
      (N.formInChart x (α p.1) (g p)) (fun _ => fderiv ℝ g p (vs 0))
    congr 1
    funext i
    rw [Fin.eq_zero i]
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
  dsimp only [formInChart, realPullbackCovectorInChart]
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
the native interval covector, including all time and spatial directions. -/
theorem intervalCovectorInChart_nativeTotalCovector_realMap {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e)
    (f : ℝ → M.Point → N.Point)
    (hf : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞
      (fun q : ℝ × M.Point => f q.1 q.2))
    (α : Parameter → N.Form 1) (β : ℝ → N.Form 1)
    (heq : ∀ t, β t.val = α t) (a : M.Point) (t : Parameter) (y : Model d) :
    M.intervalCovectorInChart
      (nativeTotalCovector ((𝓡∂ 1).prod 𝓘(ℝ, Model d)) N Prod.fst
        (fun p : Parameter × M.Point => f p.1.val p.2) α) a t y =
      M.realPullbackCovectorInChart N f β a (t.val, y) := by
  ext vs
  dsimp only [intervalCovectorInChart, nativeTotalCovector, realPullbackCovectorInChart]
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

/-- Full interval covector coefficients have one real smooth extension in
every spatial chart, agreeing on the indicated open spatial patch. -/
def HasRealIntervalCovectorCoefficientsOn {d : ℕ} (M : SmoothManifold d)
    (Ω : (p : Parameter × M.Point) → TangentSpace ((𝓡∂ 1).prod 𝓘(ℝ, Model d)) p
      [⋀^Fin 1]→L[ℝ] ℝ) (A : Set M.Point) : Prop :=
  IsOpen A ∧ ∀ a, ∃ B : ℝ × Model d → (ℝ × Model d) [⋀^Fin 1]→L[ℝ] ℝ,
    SmoothNearInterval (chartAt (Model d) a).target B ∧
    ∀ (t : Parameter) y, y ∈ (chartAt (Model d) a).target →
      (chartAt (Model d) a).symm y ∈ A → M.intervalCovectorInChart Ω a t y = B (t.val, y)

/-- A real map and the existing real primitive coefficient extensions
produce the full coefficient germ of any literally matching covector. -/
theorem hasRealIntervalCovectorCoefficientsOn_of_realMap {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e)
    (f : ℝ → M.Point → N.Point)
    (hf : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞
      (fun q : ℝ × M.Point => f q.1 q.2))
    (α : Parameter → N.Form 1) (hα : N.IsSmoothIntervalFormFamily α)
    (Ω : (p : Parameter × M.Point) → TangentSpace ((𝓡∂ 1).prod 𝓘(ℝ, Model d)) p
      [⋀^Fin 1]→L[ℝ] ℝ)
    (A : Set M.Point) (hA : IsOpen A)
    (heq : ∀ p : Parameter × M.Point, p.2 ∈ A → Ω p =
      nativeTotalCovector ((𝓡∂ 1).prod 𝓘(ℝ, Model d)) N Prod.fst
        (fun p : Parameter × M.Point => f p.1.val p.2) α p) :
    M.HasRealIntervalCovectorCoefficientsOn Ω A := by
  obtain ⟨β, hβ, heβ⟩ := hα
  refine ⟨hA, fun a => ⟨M.realPullbackCovectorInChart N f β a,
    M.smoothNearInterval_realPullbackCovectorInChart N f hf β hβ a, ?_⟩⟩
  intro t y _ hy
  dsimp only [intervalCovectorInChart]
  rw [heq _ hy]
  exact M.intervalCovectorInChart_nativeTotalCovector_realMap N f hf α β heβ a t y

end FsFltz.Geometry.SmoothManifold

namespace FsFltz.Geometry

section CovectorComposition
variable {E H X F G Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G] [TopologicalSpace Y]
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F G)
  [ChartedSpace H X] [ChartedSpace G Y]

/-- The full derivative of the actual patch pulls back the canonical total
covector. This identity retains any parameter component of the covector. -/
theorem nativeTotalCovector_comp {d : ℕ} (N : SmoothManifold d)
    (p : X → Parameter) (q : X → N.Point) (α : Parameter → N.Form 1)
    (hq : ContMDiff I 𝓘(ℝ, Model d) ∞ q)
    (j : Y → X) (hj : ContMDiff J I ∞ j) (y : Y) :
    (nativeTotalCovector I N p q α (j y)).compContinuousLinearMap (mfderiv J I j y) =
      nativeTotalCovector J N (p ∘ j) (q ∘ j) α y := by
  have hd := mfderiv_comp y (hq.mdifferentiableAt (by simp))
    (hj.mdifferentiableAt (by simp))
  ext vs
  dsimp only [nativeTotalCovector, Function.comp_def]
  change (α (p (j y)) (q (j y))) (fun k =>
      mfderiv I 𝓘(ℝ, Model d) q (j y) (mfderiv J I j y (vs k))) =
    (α (p (j y)) (q (j y))) (fun k =>
      mfderiv J 𝓘(ℝ, Model d) (q ∘ j) y (vs k))
  rw [hd]
  rfl

end CovectorComposition
end FsFltz.Geometry

namespace FsFltz.Geometry.PairDeformation
open SmoothManifold IntrinsicCompletionGluing IntrinsicLiouville

variable {k n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- The same original total covector has actual real open full coefficients
in its full-cylinder patch on a uniform seam/outward strip. Its time
component is obtained from the full real cylinder differential. -/
theorem exists_ambientNativeCylinderCovector_coefficients
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
    let Ω := nativeTotalCovector (familyModel (k + 1))
      Q.source.ambientCompletion.ambient.manifold (parameter c) q Q.completedPrimitive
    ∃ a : ℝ, a < 0 ∧
      (bandManifold δ (IntrinsicBoundary.smoothManifold k M)).HasRealIntervalCovectorCoefficientsOn
        (fun p => (Ω (totalCylinder c p)).compContinuousLinearMap
          (mfderiv (familyModel (k + 1)) (familyModel (k + 1)) (totalCylinder c) p))
        {p | a < -p.val.1} := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) δ
  let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
  let P := bandManifold δ (IntrinsicBoundary.smoothManifold k M)
  let N := Q.source.ambientCompletion.ambient.manifold
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
  refine ⟨a, ha, P.hasRealIntervalCovectorCoefficientsOn_of_realMap N f hf
    Q.completedPrimitive Q.completedAmbientPrimitive_smooth _ _ hA ?_⟩
  intro p hpA
  rw [nativeTotalCovector_comp (familyModel (k + 1)) (familyModel (k + 1))
    N (parameter c) q Q.completedPrimitive hq (totalCylinder c)
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
  dsimp only [nativeTotalCovector, Function.comp_def]
  erw [hvalue, hd]

/-- The real native deformation produces full real open covector
coefficients on the whole original native interior, for the same total
covector and the actual interior-patch differential. -/
theorem ambientNativeInteriorCovector_coefficients
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
    let Ω := nativeTotalCovector (familyModel (k + 1))
      Q.source.ambientCompletion.ambient.manifold (parameter c) q Q.completedPrimitive
    (IntrinsicInterior.smoothManifold k M).HasRealIntervalCovectorCoefficientsOn
      (fun p => (Ω (totalInterior c p)).compContinuousLinearMap
        (mfderiv (familyModel (k + 1)) (familyModel (k + 1)) (totalInterior c) p)) univ := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
  let P := IntrinsicInterior.smoothManifold k M
  let N := Q.source.ambientCompletion.ambient.manifold
  let f₀ : M → N.Point := fun x => Q.source.ambientCompletion.inclusion.map (e parameterZero x).val
  have hf₀ : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) ∞ f₀ :=
    Q.source.ambientCompletion.inclusion.map.contMDiff.comp
      (Q.source.ambientDomain.domain.contMDiff_subtype_val.comp (e parameterZero).contMDiff)
  let f : ℝ → P.Point → N.Point := fun t x => f₀ (R t x.val)
  have hf : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
      𝓘(ℝ, Model (2 * n)) ∞ (fun p : ℝ × P.Point => f p.1 p.2) :=
    hf₀.comp (hR.1.comp (contMDiff_id.prodMap IntrinsicInterior.contMDiff_val))
  apply P.hasRealIntervalCovectorCoefficientsOn_of_realMap N f hf
    Q.completedPrimitive Q.completedAmbientPrimitive_smooth _ univ isOpen_univ
  intro p _
  rw [nativeTotalCovector_comp (familyModel (k + 1)) (familyModel (k + 1))
    N (parameter c) q Q.completedPrimitive hq (totalInterior c)
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

namespace FsFltz.Geometry.IntrinsicCompletionGluing

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]

/-- The original native interior and any seam/outward strip with a
negative cutoff cover the original completed family. Deeper inward
cylinder points use their literally equal native interior representatives. -/
theorem totalInterior_cylinder_strip_cover {δ : ℝ} (hδ : 0 < δ)
    (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
    (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
      (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
    (hzero : ∀ t x, C t (0, x) = x.val)
    (a : ℝ) (ha : a < 0)
    (z : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) :
    (∃ p, totalInterior (fun t p => C t p.val) p = z) ∨
      ∃ p, a < -p.2.val.1 ∧ totalCylinder (fun t p => C t p.val) p = z := by
  let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
  rcases totalInterior_cylinder_cover hδ c hzero z with hi | ⟨p, hp⟩
  · exact Or.inl hi
  · by_cases hs : a < -p.2.val.1
    · exact Or.inr ⟨p, hs, hp⟩
    · have hpos : 0 < p.2.val.1 := by linarith
      have hi : (𝓡∂ (k + 1)).IsInteriorPoint (c p.1 (halfOfNonneg p.2 hpos.le)) := by
        apply ((𝓡∂ (k + 1)).isInteriorPoint_iff_not_isBoundaryPoint _).mpr
        intro hb
        have hz := (hboundary p.1 (halfOfNonneg p.2 hpos.le)).mp hb
        change p.2.val.1 = 0 at hz
        linarith
      let x : IntrinsicInterior.Point k M := ⟨c p.1 (halfOfNonneg p.2 hpos.le), hi⟩
      refine Or.inl ⟨(p.1, x), ?_⟩
      exact ((totalInterior_eq_totalCylinder_iff c hboundary (p.1, x) p).mpr
        ⟨rfl, hpos, rfl⟩).trans hp

end FsFltz.Geometry.IntrinsicCompletionGluing
