import FsFltz.Geometry.Liouville
import FsFltz.Geometry.LocalInverse
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Straightening regular boundary equations

Source: `geoemtric-part-fsf.tex`, conventions and `def:pair`, lines 119–160;
`sec:lean`, lines 783–814. The inverse function theorem straightens an actual
regular defining function, preserving the domain and its frontier. This is
a local boundary foundation, not a construction of a Liouville completion.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry

/-- Straighten a scalar function using its own nonzero differential. Both
directions are smooth on open sets, with exact equality of the functions. -/
theorem exists_scalar_straightening
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → ℝ} {U : Set E} {a : E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (ha : a ∈ U)
    (hregular : fderiv ℝ f a ≠ 0) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      a ∈ e.source ∧ e.source ⊆ U ∧
      ∀ y ∈ e.source, fderiv ℝ f a (e y) = f y := by
  let L := fderiv ℝ f a
  obtain ⟨v, hv⟩ : ∃ v, L v ≠ 0 := by
    by_contra! h
    exact hregular (ContinuousLinearMap.ext h)
  let w := (L v)⁻¹ • v
  have hw : L w = 1 := by simp [w, hv]
  let g : E → E := fun y => y + (f y - L y) • w
  have hg : ContDiffOn ℝ ∞ g U :=
    contDiffOn_id.add ((hf.sub L.contDiff.contDiffOn).smul contDiffOn_const)
  have hdf := (hf.contDiffAt (hU.mem_nhds ha)).differentiableAt (by simp)
  have hdg : HasFDerivAt g (ContinuousLinearMap.id ℝ E) a := by
    have h := (hasFDerivAt_id a).add ((hdf.hasFDerivAt.sub L.hasFDerivAt).smul_const w)
    convert h using 1 <;> simp [g, L]
    funext y
    rfl
  have hlocal := isLocalDiffeomorphAt_of_bijective_mfderiv_manifold hU
    hg.contMDiffOn ha (by rw [mfderiv_eq_fderiv, hdg.fderiv]; exact Function.bijective_id)
  obtain ⟨e, hae, he⟩ := hlocal
  let r := e.toOpenPartialHomeomorph.restrOpen U hU
  let e' : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
    { r.toPartialEquiv with
      open_source := r.open_source
      open_target := r.open_target
      contMDiffOn_toFun := e.contMDiffOn_toFun.mono inter_subset_left
      contMDiffOn_invFun := e.contMDiffOn_invFun.mono inter_subset_left }
  refine ⟨e', ⟨hae, ha⟩, inter_subset_right, ?_⟩
  intro y hy
  change L (e y) = f y
  rw [← he hy.1]
  simp only [g, map_add, map_smul, hw, smul_eq_mul, mul_one]
  ring

/-- Restrict corresponding subsets of an open partial homeomorphism. They
need not be open in the ambient spaces; sources are open in the subtypes. -/
theorem exists_openPartialHomeomorph_subtypes
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {s : Set X} {t : Set Y}
    (h : e.IsImage s t) (x₀ : s) (y₀ : t) :
    ∃ r : OpenPartialHomeomorph s t,
      r.source = Subtype.val ⁻¹' e.source ∧
      r.target = Subtype.val ⁻¹' e.target ∧
      (∀ x ∈ r.source, (r x).val = e x.val) ∧
      (∀ y ∈ r.target, (r.symm y).val = e.symm y.val) := by
  classical
  let f : s → t := fun x =>
    if hx : x.val ∈ e.source then ⟨e x.val, (h hx).mpr x.property⟩ else y₀
  let g : t → s := fun y =>
    if hy : y.val ∈ e.target then ⟨e.symm y.val, (h.symm_apply_mem_iff hy).mpr y.property⟩
    else x₀
  have hf (x : s) (hx : x.val ∈ e.source) : (f x).val = e x.val := by simp [f, hx]
  have hg (y : t) (hy : y.val ∈ e.target) : (g y).val = e.symm y.val := by simp [g, hy]
  have hfm : MapsTo f (Subtype.val ⁻¹' e.source) (Subtype.val ⁻¹' e.target) := by
    intro x hx
    change (f x).val ∈ e.target
    rw [hf x hx]
    exact e.map_source hx
  have hgm : MapsTo g (Subtype.val ⁻¹' e.target) (Subtype.val ⁻¹' e.source) := by
    intro y hy
    change (g y).val ∈ e.source
    rw [hg y hy]
    exact e.map_target hy
  let r : OpenPartialHomeomorph s t :=
    { toFun := f
      invFun := g
      source := Subtype.val ⁻¹' e.source
      target := Subtype.val ⁻¹' e.target
      map_source' := hfm
      map_target' := hgm
      left_inv' := by
        intro x hx
        apply Subtype.ext
        rw [hg _ (hfm hx), hf x hx, e.left_inv hx]
      right_inv' := by
        intro y hy
        apply Subtype.ext
        rw [hf _ (hgm hy), hg y hy, e.right_inv hy]
      open_source := e.open_source.preimage continuous_subtype_val
      open_target := e.open_target.preimage continuous_subtype_val
      continuousOn_toFun := Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
        ((e.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hx => hx)).congr
          (fun x hx => hf x hx))
      continuousOn_invFun := Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
        ((e.continuousOn_symm.comp continuous_subtype_val.continuousOn (fun _ hy => hy)).congr
          (fun y hy => hg y hy)) }
  exact ⟨r, rfl, rfl, hf, hg⟩

namespace BoundaryDefiningFunction

/-- Regularity excludes a boundary point in dimension zero. -/
theorem dimension_ne_zero {d : ℕ} {M : SmoothManifold d}
    {s : Set M.Point} {x : M.Point} (B : BoundaryDefiningFunction M s x) : d ≠ 0 := by
  intro hd
  subst d
  apply B.regular
  ext v
  have hv : v = 0 := by
    exact PiLp.ext (fun i => Fin.elim0 i)
  simp [hv]

/-- A regular boundary equation becomes an exact linear half-space equation
in a smooth chart, including smooth inverse extension across the boundary. -/
theorem exists_linear_straightening {d : ℕ} {M : SmoothManifold d}
    {s : Set M.Point} {x : M.Point} (B : BoundaryDefiningFunction M s x) :
    ∃ (L : Model d →L[ℝ] ℝ)
      (e : PartialDiffeomorph 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) M.Point (Model d) ∞),
      L ≠ 0 ∧ x ∈ e.source ∧ e.source ⊆ B.neighbourhood ∧
      (∀ y ∈ e.source, L (e y) = B.rho y) := by
  let c := chartAt (Model d) x
  let f : Model d → ℝ := B.rho ∘ c.symm
  let U := c.target ∩ c.symm ⁻¹' B.neighbourhood
  have hU : IsOpen U := c.continuousOn_symm.isOpen_inter_preimage c.open_target
    B.open_neighbourhood
  have hc : x ∈ c.source := mem_chart_source _ x
  have ha : c x ∈ U := by
    refine ⟨c.map_source hc, ?_⟩
    change c.symm (c x) ∈ B.neighbourhood
    rw [c.left_inv hc]
    exact B.mem_neighbourhood
  have hf : ContDiffOn ℝ ∞ f U := by
    apply ContMDiffOn.contDiffOn
    exact B.smooth_rho.comp
      ((contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d)) (n := ∞) (x := x)).mono
        inter_subset_left) inter_subset_right
  have hrho := (B.smooth_rho.contMDiffAt
    (B.open_neighbourhood.mem_nhds B.mem_neighbourhood)).mdifferentiableAt (by simp)
  have hcs := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) x).symm
  have hd : fderiv ℝ f (c x) =
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) B.rho x).comp
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c.symm (c x)) := by
    rw [← mfderiv_eq_fderiv]
    have h := mfderiv_comp (f := c.symm) (g := B.rho) (c x)
      (by simpa only [c.left_inv hc] using hrho) (hcs.mdifferentiableAt ha.1)
    change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) f (c x) =
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) B.rho (c.symm (c x))).comp
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c.symm (c x)) at h
    rw [c.left_inv hc] at h
    exact h
  have hregular : fderiv ℝ f (c x) ≠ 0 := by
    intro hz
    apply B.regular
    ext v
    obtain ⟨w, hw⟩ := (hcs.mfderiv_bijective ha.1).2 v
    have hh := congrArg (fun A : Model d →L[ℝ] ℝ => A w) hz
    rw [hd] at hh
    change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) B.rho x
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c.symm (c x) w) = 0 at hh
    rwa [hw] at hh
  obtain ⟨e, hae, heU, heq⟩ := exists_scalar_straightening hU hf ha hregular
  let c' : PartialDiffeomorph 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) M.Point (Model d) ∞ :=
    { c.toPartialEquiv with
      open_source := c.open_source
      open_target := c.open_target
      contMDiffOn_toFun := contMDiffOn_chart
      contMDiffOn_invFun := contMDiffOn_chart_symm }
  refine ⟨fderiv ℝ f (c x), c'.trans e, hregular, ⟨hc, hae⟩, ?_, ?_⟩
  · intro y hy
    change y ∈ c.source ∧ c y ∈ e.source at hy
    have h := (heU hy.2).2
    change c.symm (c y) ∈ B.neighbourhood at h
    rwa [c.left_inv hy.1] at h
  · intro y hy
    change y ∈ c.source ∧ c y ∈ e.source at hy
    change fderiv ℝ f (c x) (e (c y)) = B.rho y
    rw [heq _ hy.2]
    exact congrArg B.rho (c.left_inv hy.1)

/-- The chart identifies the entire local domain and its frontier, not only
their tangent spaces. -/
theorem exists_linear_halfspace_chart {d : ℕ} {M : SmoothManifold d}
    {s : Set M.Point} {x : M.Point} (B : BoundaryDefiningFunction M s x) :
    ∃ (L : Model d →L[ℝ] ℝ)
      (e : PartialDiffeomorph 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) M.Point (Model d) ∞),
      L ≠ 0 ∧ x ∈ e.source ∧ e.source ⊆ B.neighbourhood ∧
      (∀ y ∈ e.source, L (e y) = B.rho y) ∧
      e '' (s ∩ e.source) = e.target ∩ {v | L v ≤ 0} ∧
      e '' (frontier s ∩ e.source) = e.target ∩ {v | L v = 0} := by
  obtain ⟨L, e, hL, hx, hU, hρ⟩ := B.exists_linear_straightening
  refine ⟨L, e, hL, hx, hU, hρ, ?_, ?_⟩
  · ext v
    constructor
    · rintro ⟨y, ⟨hy, hye⟩, rfl⟩
      exact ⟨e.map_source' hye, (hρ y hye).trans_le ((B.sublevel y (hU hye)).mp hy)⟩
    · rintro ⟨hv, hLv⟩
      have hy := e.map_target' hv
      refine ⟨e.invFun v, ⟨?_, hy⟩, e.right_inv' hv⟩
      apply (B.sublevel _ (hU hy)).mpr
      rw [← hρ _ hy, e.right_inv' hv]
      exact hLv
  · ext v
    constructor
    · rintro ⟨y, ⟨hy, hye⟩, rfl⟩
      exact ⟨e.map_source' hye, (hρ y hye).trans ((B.zero_level y (hU hye)).mp hy)⟩
    · rintro ⟨hv, hLv⟩
      have hy := e.map_target' hv
      refine ⟨e.invFun v, ⟨?_, hy⟩, e.right_inv' hv⟩
      apply (B.zero_level _ (hU hy)).mpr
      rw [← hρ _ hy, e.right_inv' hv]
      exact hLv

/-- A nonzero real functional can be made the first Euclidean coordinate. -/
theorem exists_linearEquiv_first_coordinate {d : ℕ} [NeZero d]
    (L : Model d →L[ℝ] ℝ) (hL : L ≠ 0) :
    ∃ A : Model d ≃L[ℝ] Model d, ∀ v, (A v) 0 = L v := by
  classical
  let e : Model d := EuclideanSpace.single 0 1
  have he : e 0 = 1 := by simp [e]
  obtain ⟨w, hw0, hwL⟩ : ∃ w : Model d, w 0 = 1 ∧ L w ≠ 0 := by
    by_cases h : L e ≠ 0
    · exact ⟨e, he, h⟩
    · have heL : L e = 0 := not_ne_iff.mp h
      obtain ⟨v, hv⟩ : ∃ v, L v ≠ 0 := by
        by_contra hn
        apply hL
        ext v
        simpa using not_exists.mp hn v
      refine ⟨e + v - (v 0) • e, ?_, ?_⟩
      · simp [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, he]
      · simpa [map_add, map_sub, map_smul, heL] using hv
  let p : Model d →L[ℝ] ℝ := (ContinuousLinearMap.proj (0 : Fin d)).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap
  have hp (v : Model d) : p v = v 0 := rfl
  let f : Module.Dual ℝ (Model d) := L.toLinearMap - p.toLinearMap
  have hu : IsUnit (1 + f w) := by
    apply isUnit_iff_ne_zero.mpr
    simpa [f, hp, hw0] using hwL
  let A : Model d ≃L[ℝ] Model d :=
    (LinearEquiv.dilatransvection (f := f) (v := w) hu).toContinuousLinearEquiv
  refine ⟨A, fun v => ?_⟩
  change (v + f v • w) 0 = L v
  simp [PiLp.add_apply, PiLp.smul_apply, f, hp, hw0]

/-- A smooth ambient chart with the inward coordinate exactly minus the
defining function. No choice of boundary or completion collar is assumed. -/
theorem exists_standard_straightening {d : ℕ} [NeZero d] {M : SmoothManifold d}
    {s : Set M.Point} {x : M.Point} (B : BoundaryDefiningFunction M s x) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) M.Point (Model d) ∞,
      x ∈ e.source ∧ e.source ⊆ B.neighbourhood ∧
      ∀ y ∈ e.source, (e y) 0 = -B.rho y := by
  obtain ⟨L, e, hL, hx, hU, hρ⟩ := B.exists_linear_straightening
  obtain ⟨A, hA⟩ := exists_linearEquiv_first_coordinate (-L) (neg_ne_zero.mpr hL)
  refine ⟨e.trans A.toDiffeomorph.toPartialDiffeomorph, ⟨hx, mem_univ _⟩,
    fun y hy => hU hy.1, ?_⟩
  intro y hy
  change (A (e y)) 0 = -B.rho y
  rw [hA]
  change -L (e y) = -B.rho y
  rw [hρ y hy.1]

/-- An actual chart of the domain subtype into the standard Euclidean
half-space. The supplied ambient partial diffeomorphism is a smooth
extension of the chart and its inverse across the boundary. -/
theorem exists_halfspace_chart {d : ℕ} [NeZero d] {M : SmoothManifold d}
    {s : Set M.Point} {x : M.Point} (B : BoundaryDefiningFunction M s x) (hx : x ∈ s) :
    ∃ (e : PartialDiffeomorph 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) M.Point (Model d) ∞)
      (r : OpenPartialHomeomorph s (EuclideanHalfSpace d)),
      x ∈ e.source ∧ e.source ⊆ B.neighbourhood ∧
      r.source = Subtype.val ⁻¹' e.source ∧
      r.target = Subtype.val ⁻¹' e.target ∧
      (∀ y ∈ r.source, (r y).val = e y.val) ∧
      (∀ v ∈ r.target, (r.symm v).val = e.invFun v.val) ∧
      (∀ y ∈ e.source, (e y) 0 = -B.rho y) ∧
      (∀ y ∈ r.source, y.val ∈ frontier s ↔ (r y).val 0 = 0) := by
  obtain ⟨e, hxe, hU, hρ⟩ := B.exists_standard_straightening
  have hi : e.toOpenPartialHomeomorph.IsImage s {v : Model d | 0 ≤ v 0} := by
    intro y hy
    change 0 ≤ (e y) 0 ↔ y ∈ s
    rw [hρ y hy, neg_nonneg]
    exact (B.sublevel y (hU hy)).symm
  obtain ⟨r, hrs, hrt, hrf, hrg⟩ :=
    exists_openPartialHomeomorph_subtypes e.toOpenPartialHomeomorph hi ⟨x, hx⟩
      (⟨0, by simp⟩ : EuclideanHalfSpace d)
  refine ⟨e, r, hxe, hU, hrs, hrt, hrf, hrg, hρ, ?_⟩
  intro y hy
  have hye : y.val ∈ e.source := by
    rw [hrs] at hy
    exact hy
  rw [hrf y hy]
  change y.val ∈ frontier s ↔ (e y.val) 0 = 0
  rw [hρ _ hye, neg_eq_zero]
  exact B.zero_level _ (hU hye)

end BoundaryDefiningFunction

namespace CompactDomain

/-- Every actual boundary point of a compact regular-sublevel presentation
admits a native half-space chart with smooth ambient extensions in both
directions. The zero-dimensional case has no such boundary point. -/
theorem exists_boundary_halfspace_chart {d : ℕ} (D : CompactDomain d)
    (x : D.extension.Point) (hx : x ∈ frontier D.carrier) :
    ∃ hd : NeZero d,
      ∃ r : OpenPartialHomeomorph D.Point (@EuclideanHalfSpace d hd),
        (⟨x, D.compact.isClosed.frontier_subset hx⟩ : D.Point) ∈ r.source ∧
        ∃ e : PartialDiffeomorph 𝓘(ℝ, Model d) 𝓘(ℝ, Model d)
          D.extension.Point (Model d) ∞,
          r.source = Subtype.val ⁻¹' e.source ∧
          r.target = Subtype.val ⁻¹' e.target ∧
          (∀ y ∈ r.source, (r y).val = e y.val) ∧
          (∀ v ∈ r.target, (r.symm v).val = e.invFun v.val) ∧
          (∀ y ∈ r.source, y.val ∈ frontier D.carrier ↔ (r y).val 0 = 0) := by
  let B := D.defining x hx
  let hd : NeZero d := ⟨B.dimension_ne_zero⟩
  obtain ⟨e, r, hxe, _, hrs, hrt, hrf, hrg, _, hb⟩ :=
    B.exists_halfspace_chart (D.compact.isClosed.frontier_subset hx)
  refine ⟨hd, r, ?_, e, hrs, hrt, hrf, hrg, hb⟩
  rw [hrs]
  exact hxe

end CompactDomain
end FsFltz.Geometry
