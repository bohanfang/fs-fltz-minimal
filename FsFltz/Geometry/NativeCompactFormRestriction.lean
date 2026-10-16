import FsFltz.Geometry.BoundaryAtlas
import FsFltz.Geometry.IntrinsicExteriorNaturality
import FsFltz.Geometry.IntrinsicPrimitiveFamilyExtension
import FsFltz.Geometry.Deformation

/-!
# Restriction of smooth ambient forms to the actual native compact domain

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, `def:chain`,
lines 163–199, and `sec:lean`, lines 788–814. The regular-sublevel domain's
extended half-space charts give real open extensions of the coefficients of
the actual differential pullback. The family result includes real open
extensions across the closed parameter interval's endpoints.

This proves primitive regularity for restriction to a native compact domain.
It does not assemble a reverse presentation of a whole Liouville pair family.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.CompactDomain

variable {k : ℕ} (D : CompactDomain (k + 1))

/-- Restriction is the actual manifold-differential pullback through the
inclusion of the compact domain into its ambient extension. -/
def restrictForm {r : ℕ} (η : D.extension.Form r) :
    IntrinsicLiouville.Form k D.Point r :=
  fun x => (η x.val).compContinuousLinearMap
    (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
      (Subtype.val : D.Point → D.extension.Point) x)

/-- The target of an extended native chart is the ambient chart target
intersected with the actual half-space range. -/
theorem ExtendedHalfSpaceChart.extend_target_eq
    (c : ExtendedHalfSpaceChart D) :
    (c.chart.extend (𝓡∂ (k + 1))).target =
      c.extension.target ∩ range (𝓡∂ (k + 1)) := by
  rw [c.chart.extend_target, c.target_eq]
  ext y
  constructor
  · rintro ⟨hy, hyr⟩
    have hval : ((𝓡∂ (k + 1)).symm y).val = y := (𝓡∂ (k + 1)).right_inv hyr
    exact ⟨by simpa only [mem_preimage, hval] using hy, hyr⟩
  · rintro ⟨hy, hyr⟩
    have hval : ((𝓡∂ (k + 1)).symm y).val = y := (𝓡∂ (k + 1)).right_inv hyr
    exact ⟨by simpa only [mem_preimage, hval] using hy, hyr⟩

/-- The inclusion composed with the native inverse chart agrees with the
specified smooth ambient inverse on the entire native chart target. -/
theorem ExtendedHalfSpaceChart.val_extend_symm
    (c : ExtendedHalfSpaceChart D) {y : Model (k + 1)}
    (hy : y ∈ (c.chart.extend (𝓡∂ (k + 1))).target) :
    ((c.chart.extend (𝓡∂ (k + 1))).symm y).val = c.extension.invFun y := by
  have hyr := c.chart.extend_target_subset_range hy
  have hval : ((𝓡∂ (k + 1)).symm y).val = y := (𝓡∂ (k + 1)).right_inv hyr
  rw [c.chart.extend_target] at hy
  have hct : (𝓡∂ (k + 1)).symm y ∈ c.chart.target := hy.1
  change (c.chart.symm ((𝓡∂ (k + 1)).symm y)).val = _
  rw [c.invFun_eq _ hct, hval]

/-- The real ambient chart extension computes the actual coefficients of
the restricted form, with its ordinary spatial derivative even at the native
boundary. This identifies the extension; it is not an extra form witness. -/
theorem formInChart_restrictForm {r : ℕ} (η : D.extension.Form r)
    (c : ExtendedHalfSpaceChart D) (a : D.extension.Point)
    {y : Model (k + 1)}
    (hy : y ∈ (c.chart.extend (𝓡∂ (k + 1))).target)
    (ha : c.extension.invFun y ∈ (chartAt (Model (k + 1)) a).source) :
    IntrinsicLiouville.formInChart c.chart (D.restrictForm η) y =
      (D.extension.formInChart a η
        ((chartAt (Model (k + 1)) a ∘ c.extension.invFun) y)).compContinuousLinearMap
          (fderiv ℝ (chartAt (Model (k + 1)) a ∘ c.extension.invFun) y) := by
  let g := chartAt (Model (k + 1)) a ∘ c.extension.invFun
  let g₀ := chartAt (Model (k + 1)) a ∘
    (Subtype.val : D.Point → D.extension.Point) ∘
      (c.chart.extend (𝓡∂ (k + 1))).symm
  have hcy : y ∈ c.extension.target := (c.extend_target_eq D ▸ hy).1
  have hgi := c.extension.contMDiffOn_invFun.contMDiffAt
    (c.extension.open_target.mem_nhds hcy)
  have hgb := (contMDiffOn_chart (I := 𝓘(ℝ, Model (k + 1)))
    (n := ∞) (x := a)).contMDiffAt
    ((chartAt (Model (k + 1)) a).open_source.mem_nhds ha)
  have hg : ContDiffAt ℝ ∞ g y := (hgb.comp y hgi).contDiffAt
  have heq : g₀ =ᶠ[𝓝[range (𝓡∂ (k + 1))] y] g := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds
      (c.extension.open_target.mem_nhds hcy), self_mem_nhdsWithin] with z hzc hzr
    have hz : z ∈ (c.chart.extend (𝓡∂ (k + 1))).target := by
      rw [c.extend_target_eq D]
      exact ⟨hzc, hzr⟩
    simp only [g₀, g, Function.comp_apply, c.val_extend_symm D hz]
  have heqy : g₀ y = g y := by
    simp only [g₀, g, Function.comp_apply, c.val_extend_symm D hy]
  have hd : fderivWithin ℝ g₀ (range (𝓡∂ (k + 1))) y = fderiv ℝ g y := by
    rw [heq.fderivWithin_eq heqy,
      fderivWithin_eq_fderiv
        ((𝓡∂ (k + 1)).uniqueDiffOn y (c.chart.extend_target_subset_range hy))
        (hg.differentiableAt (by simp))]
  have hx : ((c.chart.extend (𝓡∂ (k + 1))).symm y).val ∈
      (chartAt (Model (k + 1)) a).source := by
    rwa [c.val_extend_symm D hy]
  unfold restrictForm
  rw [IntrinsicLiouville.formInChart_pullback_from_boundaryless D.extension
    (Subtype.val : D.Point → D.extension.Point) η (by exact ⟨c, rfl⟩) a hy hx
      (D.contMDiff_subtype_val.mdifferentiableAt (by simp)), hd]
  change (D.extension.formInChart a η (g₀ y)).compContinuousLinearMap (fderiv ℝ g y) =
    (D.extension.formInChart a η (g y)).compContinuousLinearMap (fderiv ℝ g y)
  rw [heqy]

private theorem contDiffOn_oneForm_comp {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (a : G → F [⋀^Fin 1]→L[ℝ] ℝ) (B : G → E →L[ℝ] F) (U : Set G)
    (ha : ContDiffOn ℝ ∞ a U) (hB : ContDiffOn ℝ ∞ B U) :
    ContDiffOn ℝ ∞ (fun y => (a y).compContinuousLinearMap (B y)) U := by
  let eF := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := F) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  let eE := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  have hs := eE.contDiff.comp_contDiffOn
    ((eF.symm.contDiff.comp_contDiffOn ha).clm_comp hB)
  convert hs using 1
  ext y vs
  change a y (fun i => B y (vs i)) = a y (fun _ => B y (vs 0))
  congr 1
  funext i
  rw [Fin.eq_zero i]

/-- An actual smooth ambient interval family restricts to a native family
whose chart coefficients have smooth real open extensions in time and space.
The extension is constructed from the ambient family and the boundary chart;
no geometric law is imposed outside the source parameter interval. -/
theorem isLocallyExtendibleFormFamily_restrictForm
    (η : Parameter → D.extension.Form 1)
    (hη : D.extension.IsSmoothIntervalFormFamily η) :
    IntrinsicLiouville.IsLocallyExtendibleFormFamily (fun t => D.restrictForm (η t)) := by
  obtain ⟨η', hη', hηeq⟩ := hη
  rintro e ⟨c, rfl⟩ t x hx
  let b := chartAt (Model (k + 1)) x.val
  let g := b ∘ c.extension.invFun
  let S := c.extension.target ∩ c.extension.invFun ⁻¹' b.source
  have hS : IsOpen S := c.extension.contMDiffOn_invFun.continuousOn.isOpen_inter_preimage
    c.extension.open_target b.open_source
  have hg : ContDiffOn ℝ ∞ g S :=
    ((contMDiffOn_chart (I := 𝓘(ℝ, Model (k + 1))) (n := ∞) (x := x.val)).comp
      (c.extension.contMDiffOn_invFun.mono inter_subset_left)
      (fun _ hz => hz.2)).contDiffOn
  have hgmap : MapsTo g S b.target := fun y hy => b.map_source hy.2
  have hxx : (c.chart.extend (𝓡∂ (k + 1))) x ∈ S := by
    have hy : (c.chart.extend (𝓡∂ (k + 1))) x ∈
        (c.chart.extend (𝓡∂ (k + 1))).target :=
      (c.chart.extend (𝓡∂ (k + 1))).map_source
        (by simpa only [c.chart.extend_source] using hx)
    refine ⟨(c.extend_target_eq D ▸ hy).1, ?_⟩
    change c.extension.invFun ((c.chart.extend (𝓡∂ (k + 1))) x) ∈ b.source
    rw [← c.val_extend_symm D hy, c.chart.extend_left_inv hx]
    exact mem_chart_source _ _
  obtain ⟨V, hV, hVcontains, hcoeff⟩ := hη' x.val
  let P : Set (ℝ × Model (k + 1)) := univ ×ˢ S
  let q : ℝ × Model (k + 1) → ℝ × Model (k + 1) := fun ty => (ty.1, g ty.2)
  have hP : IsOpen P := isOpen_univ.prod hS
  have hq : ContDiffOn ℝ ∞ q P :=
    contDiff_fst.contDiffOn.prodMk (hg.comp contDiff_snd.contDiffOn (fun _ hz => hz.2))
  let U := P ∩ q ⁻¹' V
  have hU : IsOpen U := hq.continuousOn.isOpen_inter_preimage hP hV
  have htx : (t.val, (c.chart.extend (𝓡∂ (k + 1))) x) ∈ U :=
    ⟨⟨mem_univ _, hxx⟩, hVcontains ⟨t.property, hgmap hxx⟩⟩
  let β : ℝ × Model (k + 1) → Model (k + 1) [⋀^Fin 1]→L[ℝ] ℝ :=
    fun ty => (D.extension.formInChart x.val (η' ty.1) (g ty.2)).compContinuousLinearMap
      (fderiv ℝ g ty.2)
  have hA : ContDiffOn ℝ ∞
      (fun ty : ℝ × Model (k + 1) => D.extension.formInChart x.val (η' ty.1) (g ty.2)) U :=
    hcoeff.comp (hq.mono inter_subset_left) (fun _ hz => hz.2)
  have hB : ContDiffOn ℝ ∞ (fun ty : ℝ × Model (k + 1) => fderiv ℝ g ty.2) U :=
    (hg.fderiv_of_isOpen hS (by simp)).comp contDiff_snd.contDiffOn
      (fun _ hz => hz.1.2)
  refine ⟨U, β, hU, htx, contDiffOn_oneForm_comp _ _ _ hA hB, ?_⟩
  intro s y hy hsy
  have hya : c.extension.invFun y ∈ b.source := hsy.1.2.2
  rw [formInChart_restrictForm D (η s) c x.val hy hya]
  simp only [β, g, b, hηeq s]

/-- Smoothness of a single ambient one-form produces local real extensions
of the actual native restricted form, including at boundary points. -/
theorem isLocallyExtendibleForm_restrictForm (η : D.extension.Form 1)
    (hη : D.extension.IsSmoothForm η) :
    IntrinsicLiouville.IsLocallyExtendibleForm (D.restrictForm η) := by
  have hfamily : D.extension.IsSmoothIntervalFormFamily (fun _ : Parameter => η) := by
    refine ⟨fun _ => η, ?_, fun _ => rfl⟩
    intro a
    refine ⟨univ ×ˢ (chartAt (Model (k + 1)) a).target,
      isOpen_univ.prod (chartAt (Model (k + 1)) a).open_target, ?_, ?_⟩
    · exact prod_mono (subset_univ _) Subset.rfl
    · exact (hη a).comp contDiff_snd.contDiffOn (fun _ hz => hz.2)
  exact (D.isLocallyExtendibleFormFamily_restrictForm (fun _ => η) hfamily).slice parameterZero

end FsFltz.Geometry.CompactDomain

namespace FsFltz.Geometry

private theorem native_primitive_family_reindex {d k : ℕ}
    (D : CompactDomain d) (hdim : d = k + 1)
    (η : Parameter → D.extension.Form 1)
    (hη : D.extension.IsSmoothIntervalFormFamily η) :
    let D' : CompactDomain (k + 1) := hdim ▸ D
    let η' : Parameter → D'.extension.Form 1 :=
      hdim.rec (motive := fun _ h => Parameter → (h ▸ D).extension.Form 1) η
    @IntrinsicLiouville.IsLocallyExtendibleFormFamily k D'.Point inferInstance
      (CompactDomain.halfSpaceChartedSpace D') 1 (fun t => D'.restrictForm (η' t)) := by
  cases hdim
  exact D.isLocallyExtendibleFormFamily_restrictForm η hη

namespace PairDeformation

/-- The ambient primitive on the deformation's fixed compact source has
native endpoint and boundary coefficient extensions. The only transport is
the stated equality of dimensions; the primitive is the actual extension
pullback already carried by the deformation. -/
theorem ambientPrimitive_native_extendible {n k : ℕ} (Q : PairDeformation n)
    (hdim : 2 * n = k + 1) :
    let D₀ := (Q.pair parameterZero).ambientDomain.domain
    let η₀ : Parameter → D₀.extension.Form 1 := fun t =>
      D₀.extension.pullback (Q.pair t).ambientDomain.domain.extension
        (Q.ambientPresentation t).extensionEquiv (Q.pair t).ambientDomain.liouville.primitive
    let D : CompactDomain (k + 1) := hdim ▸ D₀
    let η : Parameter → D.extension.Form 1 :=
      hdim.rec (motive := fun _ h => Parameter → (h ▸ D₀).extension.Form 1) η₀
    @IntrinsicLiouville.IsLocallyExtendibleFormFamily k D.Point inferInstance
      (CompactDomain.halfSpaceChartedSpace D) 1 (fun t => D.restrictForm (η t)) :=
  native_primitive_family_reindex _ hdim _ Q.ambientPrimitive_smooth

/-- The ribbon primitive on the deformation's fixed compact source has
native endpoint and boundary coefficient extensions whenever its ribbon
dimension is positive. No reverse pair-family presentation is assumed. -/
theorem ribbonPrimitive_native_extendible {n k : ℕ} (Q : PairDeformation n)
    (hdim : 2 * n - 2 = k + 1) :
    let D₀ := (Q.pair parameterZero).ribbonDomain.domain
    let η₀ : Parameter → D₀.extension.Form 1 := fun t =>
      D₀.extension.pullback (Q.pair t).ribbonDomain.domain.extension
        (Q.ribbonPresentation t).extensionEquiv (Q.pair t).ribbonDomain.liouville.primitive
    let D : CompactDomain (k + 1) := hdim ▸ D₀
    let η : Parameter → D.extension.Form 1 :=
      hdim.rec (motive := fun _ h => Parameter → (h ▸ D₀).extension.Form 1) η₀
    @IntrinsicLiouville.IsLocallyExtendibleFormFamily k D.Point inferInstance
      (CompactDomain.halfSpaceChartedSpace D) 1 (fun t => D.restrictForm (η t)) :=
  native_primitive_family_reindex _ hdim _ Q.ribbonPrimitive_smooth

end PairDeformation
end FsFltz.Geometry
