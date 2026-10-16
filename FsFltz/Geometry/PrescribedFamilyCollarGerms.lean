import FsFltz.Geometry.CompletionFamilyFields
import FsFltz.Geometry.FamilyLiouvilleLocalFlow
import FsFltz.Geometry.FlowBridge
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Collar germs of the prescribed varying completion family

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–169, and
`sec:lean`, lines 788–814. The original completed primitive family is
jointly smooth in its given presentation. Its actual transported Liouville
fields therefore have a smooth open extension near the parameter interval.
A supported parameter-preserving flow near the compact boundary seam gives
one positive two-sided integration time. ODE uniqueness identifies the
resulting jointly smooth germ with the original completion end trajectories
at every actual interval parameter, including both endpoints.

The prescribed presentation need only respect the nonnegative end. No
negative-radius square, off-interval overlap law, complete family flow, or
joint smoothness of the prescribed end maps is an input. This foundation
does not construct the original completed family or prove `thm:target`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold

namespace SmoothManifold

/-- Chartwise family regularity produces one open native-section
neighborhood of the whole interval-times-manifold. No uniform larger
parameter interval is required on a noncompact manifold. -/
theorem IsSmoothVectorFieldFamily.exists_contMDiffOn_neighborhood {d : ℕ}
    {M : SmoothManifold d} {Z : (t : ℝ) → (x : M.Point) → M.Tangent x}
    (hZ : M.IsSmoothVectorFieldFamily Z) :
    ∃ Ω : Set (ℝ × M.Point), IsOpen Ω ∧ parameterInterval ×ˢ univ ⊆ Ω ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
        (fun p : ℝ × M.Point =>
          (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point)) Ω := by
  let f := fun p : ℝ × M.Point =>
    (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point)
  let S : Set (Set (ℝ × M.Point)) := {V | IsOpen V ∧
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      (𝓘(ℝ, Model d)).tangent ∞ f V}
  have hΩ : IsOpen (⋃₀ S) := isOpen_sUnion (fun _ hV => hV.1)
  refine ⟨⋃₀ S, hΩ, ?_, ?_⟩
  · rintro ⟨t, x⟩ ⟨ht, _⟩
    obtain ⟨U, hU, hcover, hf⟩ := hZ x
    let c := chartAt (Model d) x
    let q : ℝ × M.Point → ℝ × Model d := fun p => (p.1, c p.2)
    let V := (univ ×ˢ c.source) ∩ q ⁻¹' U
    have hq : ContinuousOn q (univ ×ˢ c.source) :=
      continuousOn_fst.prodMk (c.continuousOn.comp continuousOn_snd (fun _ hp => hp.2))
    have hV : IsOpen V := hq.isOpen_inter_preimage (isOpen_univ.prod c.open_source) hU
    have hpV : (t, x) ∈ V :=
      ⟨⟨mem_univ _, mem_chart_source _ _⟩,
        hcover ⟨ht, c.map_source (mem_chart_source _ _)⟩⟩
    have hVf : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
        (𝓘(ℝ, Model d)).tangent ∞ f V := by
      intro p hp
      exact (M.contMDiffAt_familySection_of_chart Z x p hp.1.2
        (hf.contDiffAt (hU.mem_nhds hp.2))).contMDiffWithinAt
    exact mem_sUnion.mpr ⟨V, ⟨hV, hVf⟩, hpV⟩
  · intro p hp
    obtain ⟨V, hV, hpV⟩ := mem_sUnion.mp hp
    exact (hV.2.contMDiffAt (hV.1.mem_nhds hpV)).contMDiffWithinAt

/-- Every actual interval slice of a smooth family is an actual smooth
vector field on the entire manifold. -/
theorem IsSmoothVectorFieldFamily.slice {d : ℕ} {M : SmoothManifold d}
    {Z : (t : ℝ) → (x : M.Point) → M.Tangent x}
    (hZ : M.IsSmoothVectorFieldFamily Z) (t : Parameter) :
    M.IsSmoothVectorField (Z t.val) := by
  intro a y hy
  obtain ⟨U, hU, hcover, hf⟩ := hZ a
  exact ((hf.contDiffAt (hU.mem_nhds (hcover (show (t.val, y) ∈
    parameterInterval ×ˢ (chartAt (Model d) a).target from ⟨t.property, hy⟩)))).comp y
    (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt

end SmoothManifold

/-- A smooth radius cap retains every inward radius and is bounded on
the outward half-line. It is used only above a small negative cutoff. -/
theorem exists_smooth_capped_collar_radius (δ : ℝ) (hδ : 0 < δ) :
    ∃ s : ℝ → ℝ, ContDiff ℝ ∞ s ∧
      (∀ r, r ≤ δ / 4 → s r = r) ∧
      (∀ r, 0 ≤ r → 0 ≤ s r ∧ s r < δ) := by
  let θ : ℝ → ℝ := fun r => Real.smoothTransition (4 * r / δ - 1)
  have hθ : ContDiff ℝ ∞ θ :=
    Real.smoothTransition.contDiff.comp
      (((contDiff_const.mul contDiff_id).div_const δ).sub contDiff_const)
  have hθbounds (r : ℝ) : 0 ≤ θ r ∧ θ r ≤ 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hθzero (r : ℝ) (hr : r ≤ δ / 4) : θ r = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    have hr' : 4 * r ≤ δ := by linarith
    have := (div_le_one hδ).mpr hr'
    linarith
  have hθone (r : ℝ) (hr : δ / 2 ≤ r) : θ r = 1 := by
    apply Real.smoothTransition.one_of_one_le
    have hr' : 2 * δ ≤ 4 * r := by linarith
    have := (le_div_iff₀ hδ).mpr hr'
    linarith
  let s : ℝ → ℝ := fun r => (1 - θ r) * r + θ r * (δ / 2)
  refine ⟨s, ((contDiff_const.sub hθ).mul contDiff_id).add
    (hθ.mul contDiff_const), ?_, ?_⟩
  · intro r hr
    simp only [s, hθzero r hr, sub_zero, one_mul, zero_mul, add_zero]
  · intro r hr
    by_cases hsmall : r ≤ δ / 4
    · have he : s r = r := by simp only [s, hθzero r hsmall, sub_zero,
        one_mul, zero_mul, add_zero]
      rw [he]
      exact ⟨hr, by linarith⟩
    · by_cases hlarge : δ / 2 ≤ r
      · have he : s r = δ / 2 := by simp only [s, hθone r hlarge, sub_self,
          zero_mul, one_mul, zero_add]
        rw [he]
        constructor <;> linarith
      · have hb := hθbounds r
        have hsnonneg : 0 ≤ s r := add_nonneg
          (mul_nonneg (sub_nonneg.mpr hb.2) hr) (mul_nonneg hb.1 (by linarith))
        have hsle : s r ≤ δ / 2 := by
          have hm := mul_nonneg (sub_nonneg.mpr hb.2)
            (show 0 ≤ δ / 2 - r by linarith)
          dsimp only [s]
          nlinarith
        exact ⟨hsnonneg, lt_of_le_of_lt hsle (by linarith)⟩

namespace CompletionPresentationEquiv

variable {d : ℕ} {D E : LiouvilleDomain d}
  {C : Completion D} {C' : Completion E}
  {h : DomainPresentationEquiv D.domain E.domain}

/-- The original end trajectory transported to its prescribed reference
presentation, for all real flow times. -/
def prescribedEndMap (p : CompletionPresentationEquiv C C' h)
    (q : D.domain.boundary.Point × ℝ) : C.ambient.manifold.Point :=
  p.equiv.symm (C'.endMap (h.boundaryEquiv q.1, q.2))

/-- The nonnegative presentation square fixes the seam exactly. -/
theorem prescribedEndMap_nonnegative (p : CompletionPresentationEquiv C C' h)
    (x : D.domain.boundary.Point) (r : ℝ) (hr : 0 ≤ r) :
    p.prescribedEndMap (x, r) = C.endMap (x, r) := by
  rw [prescribedEndMap, ← p.end_square x r hr]
  exact p.equiv.left_inv _

/-- The prescribed transported trajectory solves the actual transported
Liouville field, independently of any family regularity. -/
theorem isMIntegralCurve_prescribedEndMap (p : CompletionPresentationEquiv C C' h)
    (x : D.domain.boundary.Point) :
    IsMIntegralCurve (fun r => p.prescribedEndMap (x, r))
      (C.ambient.manifold.pullbackVectorField C'.ambient.manifold p.equiv C'.ambient.field) := by
  have hcurve : IsMIntegralCurve (fun r => C'.endMap (h.boundaryEquiv x, r))
      C'.ambient.field := by
    simpa only [C'.end_flow] using
      C'.ambient.completeFlow.isMIntegralCurve
        (C'.inclusion.map (E.domain.boundaryInclusion.map (h.boundaryEquiv x)))
  intro r
  have hd := (p.equiv.symm.contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt.comp r
    (hcurve r)
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  change ℝ at a
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) p.equiv.invFun
      (C'.endMap (h.boundaryEquiv x, r))
      (a • C'.ambient.field (C'.endMap (h.boundaryEquiv x, r))) =
    a • mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) p.equiv.invFun
      (p.equiv (p.equiv.invFun (C'.endMap (h.boundaryEquiv x, r))))
      (C'.ambient.field (p.equiv (p.equiv.invFun (C'.endMap (h.boundaryEquiv x, r)))))
  have hinv : p.equiv (p.equiv.invFun (C'.endMap (h.boundaryEquiv x, r))) =
      C'.endMap (h.boundaryEquiv x, r) := p.equiv.right_inv _
  have hval := congrArg (fun z : C'.ambient.manifold.Point =>
    (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) p.equiv.invFun z
      (C'.ambient.field z) : Model d)) hinv
  simpa only [map_smul] using congrArg (fun v : Model d => a • v) hval.symm

end CompletionPresentationEquiv

namespace Completion

/-- The original varying completed primitive family produces a jointly
smooth common two-sided collar germ of its same prescribed end maps.
The positive width is uniform over the compact parameter and boundary
seam. The auxiliary extension is globally smooth, but is required to match
the original family only at actual interval parameters on this small strip. -/
theorem exists_prescribedFamily_collar_germ {d : ℕ} {D : LiouvilleDomain d}
    (C : Completion D) (E : Parameter → LiouvilleDomain d)
    (C' : ∀ t, Completion (E t))
    (h : ∀ t, DomainPresentationEquiv D.domain (E t).domain)
    (p : ∀ t, CompletionPresentationEquiv C (C' t) (h t))
    (hα : C.ambient.manifold.IsSmoothIntervalFormFamily (fun t =>
      C.ambient.manifold.pullback (C' t).ambient.manifold (p t).equiv
        (C' t).ambient.primitive)) :
    ∃ (δ : ℝ), 0 < δ ∧
      ∃ γ : ℝ → D.domain.boundary.Point × ℝ → C.ambient.manifold.Point,
        ContMDiff ((𝓘(ℝ, ℝ)).prod
            ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model d) ∞
          (fun q : ℝ × (D.domain.boundary.Point × ℝ) => γ q.1 q.2) ∧
        ∀ (t : Parameter) x r, r ∈ Ioo (-δ) δ →
          γ t.val (x, r) = (p t).prescribedEndMap (x, r) := by
  obtain ⟨Z, hZ, he⟩ :=
    C.isSmoothIntervalVectorFieldFamily_pullback_of_primitive_smooth E C' h p hα
  obtain ⟨Ω, hΩ, hcover, hΩZ⟩ := hZ.exists_contMDiffOn_neighborhood
  let seam : D.domain.boundary.Point → C.ambient.manifold.Point :=
    fun x => C.endMap (x, 0)
  have hseam : ContMDiff 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model d) ∞ seam :=
    C.smooth_endMap.comp (contMDiff_id.prodMk contMDiff_const)
  let K : Set C.ambient.manifold.Point := range seam
  have hK : IsCompact K := by
    simpa only [image_univ] using D.domain.isCompact_boundary.image hseam.continuous
  obtain ⟨U, δ, hU, _, hδ, F, hF, _, _, hlocal⟩ :=
    CollarFlow.exists_parameter_preserving_local_smoothFlow_supported Z hΩ hΩZ
      (show IsCompact parameterInterval from isCompact_Icc) hK
      (fun _ hp => hcover ⟨hp.1, mem_univ _⟩)
  let γ : ℝ → D.domain.boundary.Point × ℝ → C.ambient.manifold.Point :=
    fun t q => (F q.2 (t, seam q.1)).2
  have hγ : ContMDiff ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model d) ∞
      (fun q : ℝ × (D.domain.boundary.Point × ℝ) => γ q.1 q.2) :=
    contMDiff_snd.comp (hF.comp
      ((contMDiff_snd.comp contMDiff_snd).prodMk
        (contMDiff_fst.prodMk (hseam.comp (contMDiff_fst.comp contMDiff_snd)))))
  refine ⟨δ, hδ, γ, hγ, ?_⟩
  intro t x r hr
  have hpU : (t.val, seam x) ∈ U :=
    hU ⟨t.property, mem_range_self x⟩
  have hode : IsMIntegralCurveOn (fun u => γ t.val (x, u)) (Z t.val) (Ioo (-δ) δ) := by
    intro u hu
    exact (hlocal (t.val, seam x) hpU u hu).2.hasMFDerivWithinAt
  have hpres : IsMIntegralCurve (fun u => (p t).prescribedEndMap (x, u)) (Z t.val) := by
    rw [he t]
    exact (p t).isMIntegralCurve_prescribedEndMap x
  have hzero : γ t.val (x, 0) = (p t).prescribedEndMap (x, 0) := by
    dsimp only [γ]
    rw [F.map_zero_apply, (p t).prescribedEndMap_nonnegative x 0 (le_refl _)]
  exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (t₀ := 0) (show (0 : ℝ) ∈ Ioo (-δ) δ from ⟨by linarith, hδ⟩)
    ((hZ.slice t).contMDiff_section.of_le (by simp)) hode
    (hpres.isMIntegralCurveOn _) hzero hr

/-- A common two-sided original-family germ extends to a smooth formula
on the entire outward end above one negative cutoff. A smooth radius cap
keeps the auxiliary family within its proved germ, then the fixed reference
flow supplies the remaining outward radius. Exact matching is asserted only
at actual interval parameters and above that cutoff. -/
theorem exists_prescribedFamily_end_strip_extension {d : ℕ} {D : LiouvilleDomain d}
    (C : Completion D) (E : Parameter → LiouvilleDomain d)
    (C' : ∀ t, Completion (E t))
    (h : ∀ t, DomainPresentationEquiv D.domain (E t).domain)
    (p : ∀ t, CompletionPresentationEquiv C (C' t) (h t))
    (hα : C.ambient.manifold.IsSmoothIntervalFormFamily (fun t =>
      C.ambient.manifold.pullback (C' t).ambient.manifold (p t).equiv
        (C' t).ambient.primitive)) :
    ∃ a : ℝ, a < 0 ∧
      ∃ β : ℝ → D.domain.boundary.Point × ℝ → C.ambient.manifold.Point,
        ContMDiff ((𝓘(ℝ, ℝ)).prod
            ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model d) ∞
          (fun q : ℝ × (D.domain.boundary.Point × ℝ) => β q.1 q.2) ∧
        ∀ (t : Parameter) x r, a < r →
          β t.val (x, r) = (p t).prescribedEndMap (x, r) := by
  obtain ⟨δ, hδ, γ, hγ, heγ⟩ := C.exists_prescribedFamily_collar_germ E C' h p hα
  obtain ⟨s, hs, hseq, hsrange⟩ := exists_smooth_capped_collar_radius δ hδ
  let β : ℝ → D.domain.boundary.Point × ℝ → C.ambient.manifold.Point :=
    fun t q => C.ambient.completeFlow.flow (q.2 - s q.2) (γ t (q.1, s q.2))
  have hrad : ContMDiff ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × (D.domain.boundary.Point × ℝ) => s q.2.2) :=
    hs.contMDiff.comp (contMDiff_snd.comp contMDiff_snd)
  have hβ : ContMDiff ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model d) ∞
      (fun q : ℝ × (D.domain.boundary.Point × ℝ) => β q.1 q.2) :=
    C.ambient.completeFlow.smooth_action.comp
      (((contMDiff_snd.comp contMDiff_snd).sub hrad).prodMk
        (hγ.comp (contMDiff_fst.prodMk
          ((contMDiff_fst.comp contMDiff_snd).prodMk hrad))))
  refine ⟨-δ, by linarith, β, hβ, ?_⟩
  intro t x r hr
  by_cases hsmall : r ≤ δ / 4
  · have hrstrip : r ∈ Ioo (-δ) δ := ⟨hr, by linarith⟩
    dsimp only [β]
    rw [hseq r hsmall, sub_self, Flow.map_zero_apply]
    exact heγ t x r hrstrip
  · have hrpos : 0 ≤ r := by linarith
    have hsr := hsrange r hrpos
    have hsstrip : s r ∈ Ioo (-δ) δ := ⟨by linarith, hsr.2⟩
    dsimp only [β]
    rw [heγ t x (s r) hsstrip,
      (p t).prescribedEndMap_nonnegative x (s r) hsr.1, C.flow_endMap]
    have he : r - s r + s r = r := by ring
    rw [he]
    exact ((p t).prescribedEndMap_nonnegative x r hrpos).symm

end Completion
end FsFltz.Geometry
