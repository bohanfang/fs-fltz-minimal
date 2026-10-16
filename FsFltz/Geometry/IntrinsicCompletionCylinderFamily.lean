import FsFltz.Geometry.IntrinsicCompletionCylinder
import FsFltz.Geometry.IntrinsicPrimitiveFamilyExtension
import FsFltz.Geometry.FamilyPullback

/-!
# Joint primitive regularity on the actual completion cylinder

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 139–144,
`def:chain`, lines 163–169, and `sec:lean`, lines 788–793 and 805–814.
Native joint coefficient germs restrict to the actual intrinsic boundary.
The full cylinder primitive is then the spatial pullback of this boundary
family, multiplied by `exp(-u)` in the inward radial coordinate. All forms
remain vertical spatial forms: no parameter differential is introduced.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicBoundary

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] [T2Space M] [SecondCountableTopology M]

/-- Joint native germs produce the actual restricted boundary family,
including smooth extensions at both parameter endpoints. -/
theorem isSmoothIntervalFormFamily_restrictForm
    (α : Parameter → IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleFormFamily α) :
    (smoothManifold k M).IsSmoothIntervalFormFamily (fun t => restrictForm (α t)) := by
  classical
  let N := smoothManifold k M
  let A : Set (ℝ × N.Point) := parameterInterval ×ˢ univ
  let f : (p : ℝ × N.Point) → N.Tangent p.2 [⋀^Fin 1]→L[ℝ] ℝ := fun p =>
    if ht : p.1 ∈ parameterInterval then restrictForm (α ⟨p.1, ht⟩) p.2 else 0
  have hlocal : ∀ p ∈ A, ∃ U, IsOpen U ∧ p ∈ U ∧ ∃ g : ℝ → N.Form 1,
      N.IsSmoothFormFamilyOn g U ∧ ∀ q ∈ U ∩ A, g q.1 q.2 = f q := by
    rintro ⟨s, x⟩ ⟨hs, _⟩
    let t : Parameter := ⟨s, hs⟩
    let c := chartAt x
    have hx : x ∈ c.chart.source := mem_chartAt_source x
    have hex : x.val ∈ c.ambient.source := by rwa [c.source_eq] at hx
    obtain ⟨V, β, hV, hpV, hβ, hβeq⟩ := hα c.ambient c.mem_atlas t x.val hex
    let Q : N.Point → Model k := c.chart
    have hQ : ContMDiffOn 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) ∞ Q c.chart.source :=
      contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas ⟨c, rfl⟩)
    let P : ℝ × N.Point → ℝ × Model (k + 1) :=
      fun p => (p.1, boundaryInsert k (Q p.2))
    let U := (univ ×ˢ c.chart.source) ∩ P ⁻¹' V
    have hP : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k))
        𝓘(ℝ, ℝ × Model (k + 1)) ∞ P (univ ×ˢ c.chart.source) :=
      contMDiff_fst.contMDiffOn.prodMk_space
        ((boundaryInsert k).contDiff.contMDiff.comp_contMDiffOn
          (hQ.comp contMDiff_snd.contMDiffOn (fun _ hp => hp.2)))
    have hU : IsOpen U := hP.continuousOn.isOpen_inter_preimage
      (isOpen_univ.prod c.chart.open_source) hV
    have hcoord : c.ambient.extend (𝓡∂ (k + 1)) x.val = boundaryInsert k (Q x) := by
      have hh := c.extend_val_symm (c.chart.map_source hx)
      rwa [c.chart.left_inv hx] at hh
    have hpU : (s, x) ∈ U := ⟨⟨mem_univ _, hx⟩, by
      change (s, boundaryInsert k (Q x)) ∈ V
      rwa [hcoord] at hpV⟩
    let L := ContinuousAlternatingMap.compContinuousLinearMapCLM
      (F := ℝ) (ι := Fin 1) (boundaryInsert k)
    let β' : ℝ × Model k → Model k [⋀^Fin 1]→L[ℝ] ℝ :=
      fun p => L (β (p.1, boundaryInsert k p.2))
    let R : ℝ × Model k → ℝ × Model (k + 1) :=
      fun p => (p.1, boundaryInsert k p.2)
    have hR : ContDiff ℝ ∞ R := contDiff_fst.prodMk
      ((boundaryInsert k).contDiff.comp contDiff_snd)
    have hβ' : ContDiffOn ℝ ∞ β' (R ⁻¹' V) :=
      L.contDiff.comp_contDiffOn (hβ.comp hR.contDiffOn (fun _ hp => hp))
    let g : ℝ → N.Form 1 := fun s y => (β' (s, Q y)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) Q y)
    have hg : N.IsSmoothFormFamilyOn g U :=
      N.isSmoothFormFamilyOn_modelPullback Q c.chart.open_source hQ β'
        (hV.preimage hR.continuous) hβ'
    refine ⟨U, hU, hpU, g, hg, ?_⟩
    rintro ⟨s', y⟩ ⟨hqU, hs', _⟩
    let t' : Parameter := ⟨s', hs'⟩
    have hy : y ∈ c.chart.source := hqU.1.2
    have hyt : c.chart y ∈ c.chart.target := c.chart.map_source hy
    have hcoord' := c.extend_val_symm hyt
    rw [c.chart.left_inv hy] at hcoord'
    have htarget : boundaryInsert k (Q y) ∈ (c.ambient.extend (𝓡∂ (k + 1))).target := by
      rw [← hcoord']
      apply (c.ambient.extend (𝓡∂ (k + 1))).map_source
      simpa only [c.ambient.extend_source] using (show y.val ∈ c.ambient.source by
        rwa [c.source_eq] at hy)
    have hvalue : β' (s', Q y) =
        (restrictForm (α t') y).compContinuousLinearMap
          (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) c.chart.symm (c.chart y)) := by
      have hc := c.restrictForm_coefficients (α t') hyt
      rw [c.chart.left_inv hy] at hc
      change L (β (s', boundaryInsert k (Q y))) = _
      rw [hβeq t' _ htarget hqU.2]
      exact hc.symm
    have hd := (mdifferentiable_chart (I := 𝓘(ℝ, Model k)) x).symm_comp_deriv hy
    change (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) c.chart.symm (c.chart y)).comp
      (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) c.chart y) =
        ContinuousLinearMap.id ℝ (Model k) at hd
    dsimp only [f]
    rw [dite_eq_left hs']
    change (β' (s', Q y)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) c.chart y) = restrictForm (α t') y
    rw [hvalue]
    ext vs
    change restrictForm (α t') y (fun i =>
      ((mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) c.chart.symm (c.chart y)).comp
        (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) c.chart y)) (vs i)) = _
    rw [hd]
    rfl
  obtain ⟨lam, hlam, heq⟩ := N.exists_smoothFormFamily_extension_of_closed
    (isClosed_Icc.prod isClosed_univ) hlocal
  refine ⟨lam, hlam, ?_⟩
  intro t
  funext x
  have h := heq (t.val, x) ⟨t.property, mem_univ _⟩
  have ht : t.val ∈ parameterInterval := t.property
  simpa only [f, dite_eq_left ht] using h

end FsFltz.Geometry.IntrinsicBoundary

namespace FsFltz.Geometry.SmoothManifold

/-- A fixed smooth spatial scalar preserves joint vertical form regularity. -/
theorem IsSmoothFormFamily.function_smul {d r : ℕ} {N : SmoothManifold d}
    {α : ℝ → N.Form r} (hα : N.IsSmoothFormFamily α) {f : N.Point → ℝ}
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ f) :
    N.IsSmoothFormFamily (fun t x => f x • α t x) := by
  intro a
  obtain ⟨U, hU, hcover, hcoeff⟩ := hα a
  let V : Set (ℝ × Model d) := univ ×ˢ (chartAt (Model d) a).target
  refine ⟨U ∩ V, hU.inter (isOpen_univ.prod (chartAt (Model d) a).open_target),
    subset_inter hcover (Set.prod_mono (subset_univ _) Subset.rfl), ?_⟩
  have hs : ContDiffOn ℝ ∞
      (fun p : ℝ × Model d => f ((chartAt (Model d) a).symm p.2)) (U ∩ V) :=
    (N.contDiffOn_comp_inverseChart hf a).comp contDiffOn_snd
      (fun p hp => hp.2.2)
  apply (hs.smul (hcoeff.mono inter_subset_left)).congr
  intro p _
  ext vs
  rfl

end FsFltz.Geometry.SmoothManifold

namespace FsFltz.Geometry.IntrinsicCompletionGluing

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] [T2Space M] [SecondCountableTopology M]

/-- The actual cylinder form vanishes on every pure radial tangent:
the boundary-projection differential characterizes these tangents. -/
theorem cylinderPrimitive_radial_zero (δ : ℝ)
    (α : IntrinsicLiouville.Form k M 1)
    (p : (bandManifold δ (IntrinsicBoundary.smoothManifold k M)).Point)
    (v : (bandManifold δ (IntrinsicBoundary.smoothManifold k M)).Tangent p)
    (hv : letI := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) δ
      mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k) boundaryProjection p v = 0) :
    cylinderPrimitive δ α p (fun _ => v) = 0 := by
  let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) δ
  change Real.exp (-p.val.1) * IntrinsicBoundary.restrictForm α p.val.2
    (fun _ => mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k) boundaryProjection p v) = 0
  rw [hv, (IntrinsicBoundary.restrictForm α p.val.2).map_coord_zero (i := 0) rfl,
    mul_zero]

/-- The literal full cylinder primitive family is jointly smooth in the
parameter, radial variable, and boundary point, with only spatial tangents. -/
theorem isSmoothIntervalFormFamily_cylinderPrimitive (δ : ℝ)
    (α : Parameter → IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleFormFamily α) :
    (bandManifold δ (IntrinsicBoundary.smoothManifold k M)).IsSmoothIntervalFormFamily
      (fun t => cylinderPrimitive δ (α t)) := by
  let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) δ
  let N := bandManifold δ (IntrinsicBoundary.smoothManifold k M)
  have hb := IntrinsicBoundary.isSmoothIntervalFormFamily_restrictForm α hα
  have hp := N.isSmoothIntervalFormFamily_pullback_one_of_contMDiff_family
    (IntrinsicBoundary.smoothManifold k M) (fun _ => boundaryProjection)
    ((contMDiff_boundaryProjection δ).comp contMDiff_snd) _ hb
  obtain ⟨lam, hlam, heq⟩ := hp
  have ht : ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : N.Point => p.val.1) := contMDiff_fst.comp (contMDiff_band_val δ)
  refine ⟨fun t p => Real.exp (-p.val.1) • lam t p,
    hlam.function_smul (Real.contDiff_exp.contMDiff.comp ht.neg), ?_⟩
  intro t
  funext p
  change Real.exp (-p.val.1) • lam t.val p = cylinderPrimitive δ (α t) p
  rw [heq t]
  rfl

end FsFltz.Geometry.IntrinsicCompletionGluing
