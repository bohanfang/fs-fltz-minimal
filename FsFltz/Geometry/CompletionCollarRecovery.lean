import FsFltz.Geometry.CollarFlow
import FsFltz.Geometry.FamilyLiouvilleCollar
import FsFltz.Geometry.CompletionFamilyCollar

/-!
# Recovering a completion's compact collar from its Liouville equation

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 141–158;
`def:chain`, lines 163–169; and `sec:lean`, lines 788–814.

A supplied completion agrees with every actual Liouville collar on its
negative-radius portion. Only the compact-carrier field equation of the
completion is used. No symplecticity or identification of fields on the
whole original extension is required. Reparametrizing radius by `-u²`
places the common seam in the interior of an open time interval; uniqueness
for the suspended smooth equation then identifies the two curves.

This is a foundation about supplied completions. It does not construct
pointwise completions and proves none of `thm:target` (lines 352–415).
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold

namespace Completion

set_option backward.isDefEq.respectTransparency false in
private theorem negativeSquare_hasMFDerivAt (u : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => -s ^ 2) u
      ((1 : ℝ →L[ℝ] ℝ).smulRight (-2 * u)) := by
  have hd := ((hasDerivAt_id u).mul (hasDerivAt_id u)).neg
  have he : HasDerivAt (fun s : ℝ => -s ^ 2) (-2 * u) u := by
    convert hd using 1
    · funext s; simp [pow_two, id]
    · simp [id]; ring
  have h : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => -s ^ 2) u _ :=
    hasMFDerivAt_iff_hasFDerivAt.mpr he.hasFDerivAt
  apply h.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro s
  change ℝ at s
  erw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.toSpanSingleton_apply,
    one_apply_eq_self]

private theorem contMDiff_scaledFieldAlongProjection {d : ℕ} (M : SmoothManifold d)
    (Z : (x : M.Point) → M.Tangent x) (hZ : M.IsSmoothVectorField Z) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ((𝓘(ℝ, Model d)).tangent) ∞
      (fun p : ℝ × M.Point =>
        (⟨p.2, (-2 * p.1) • Z p.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point)) := by
  have ht : ContMDiff 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).tangent) ∞
      (fun t : ℝ => (⟨t, (0 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have hl : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      (((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)).tangent) ∞
      (fun p : ℝ × M.Point =>
        (⟨p, (0, Z p.2)⟩ :
          TangentBundle ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (ℝ × M.Point))) :=
    contMDiff_equivTangentBundleProd_symm.comp
      ((ht.comp contMDiff_fst).prodMk (hZ.contMDiff_section.comp contMDiff_snd))
  have hs : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M.Point => -2 * p.1) := contMDiff_const.mul contMDiff_fst
  exact (contMDiff_equivTangentBundleProd.comp (hs.smul_section hl)).snd

set_option backward.isDefEq.respectTransparency false in
/-- Any actual compact Liouville collar is recovered by the same completed
flow on its negative-radius part. The completion is supplied, and all field
intertwining used below is confined to the compact carrier. -/
theorem endMap_eq_inclusion_of_negative_collar {d : ℕ} {D : LiouvilleDomain d}
    (C : Completion D) (c : D.domain.boundary.Point × ℝ → D.domain.extension.Point)
    {δ : ℝ} (hδ : 0 < δ)
    (hzero : ∀ x, c (x, 0) = D.domain.boundaryInclusion.map x)
    (hcarrier : ∀ x r, r ∈ Ioc (-δ) 0 → c (x, r) ∈ D.domain.carrier)
    (hode : ∀ x r, r ∈ Ioc (-δ) 0 →
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) (fun s => c (x, s)) r
        ((1 : ℝ →L[ℝ] ℝ).smulRight (D.liouville.field (c (x, r)))))
    (x : D.domain.boundary.Point) (r : ℝ) (hr : r ∈ Ioc (-δ) 0) :
    C.endMap (x, r) = C.inclusion.map (c (x, r)) := by
  let a := Real.sqrt δ
  have ha : 0 < a := Real.sqrt_pos.mpr hδ
  have htime (u : ℝ) (hu : u ∈ Ioo (-a) a) : -u ^ 2 ∈ Ioc (-δ) 0 := by
    have hp : 0 < (a - u) * (a + u) := mul_pos (by linarith [hu.2]) (by linarith [hu.1])
    have ha₂ : a ^ 2 = δ := Real.sq_sqrt hδ.le
    constructor <;> nlinarith [sq_nonneg u]
  let γ : ℝ → C.ambient.manifold.Point :=
    fun u => C.ambient.completeFlow.flow (-u ^ 2)
      (C.inclusion.map (D.domain.boundaryInclusion.map x))
  let γ' : ℝ → C.ambient.manifold.Point := fun u => C.inclusion.map (c (x, -u ^ 2))
  have hγ (u : ℝ) (_hu : u ∈ Ioo (-a) a) :
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) γ u
        ((1 : ℝ →L[ℝ] ℝ).smulRight ((-2 * u) • C.ambient.field (γ u))) := by
    have hd := (C.ambient.completeFlow.isMIntegralCurve
      (C.inclusion.map (D.domain.boundaryInclusion.map x)) (-u ^ 2)).comp u
      (negativeSquare_hasMFDerivAt u)
    apply hd.congr_mfderiv
    apply ContinuousLinearMap.ext
    intro s
    change ℝ at s
    change (s * (-2 * u)) • C.ambient.field (γ u) =
      s • ((-2 * u) • C.ambient.field (γ u))
    rw [smul_smul]
  have hγ' (u : ℝ) (hu : u ∈ Ioo (-a) a) :
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) γ' u
        ((1 : ℝ →L[ℝ] ℝ).smulRight ((-2 * u) • C.ambient.field (γ' u))) := by
    have hd := (C.inclusion.map.contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt.comp
      (-u ^ 2) (hode x (-u ^ 2) (htime u hu))
    have he := hd.comp u (negativeSquare_hasMFDerivAt u)
    apply he.congr_mfderiv
    apply ContinuousLinearMap.ext
    intro s
    change ℝ at s
    change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) C.inclusion.map (c (x, -u ^ 2))
      ((s * (-2 * u)) • D.liouville.field (c (x, -u ^ 2))) =
      s • ((-2 * u) • C.ambient.field (γ' u))
    rw [map_smul, C.field_on_domain _ (hcarrier x _ (htime u hu)), smul_smul]
  have heq : EqOn γ γ' (Ioo (-a) a) := CollarFlow.eqOn_of_hasMFDerivAt
    (F := Model d) (Q := C.ambient.manifold.Point)
    (Z := fun u z => (-2 * u) • C.ambient.field z)
    (contMDiff_scaledFieldAlongProjection C.ambient.manifold C.ambient.field
      C.ambient.smooth_field)
    (t₀ := 0) (show (0 : ℝ) ∈ Ioo (-a) a by constructor <;> linarith)
    hγ hγ' (by simp only [γ, γ', zero_pow (by decide : (2 : ℕ) ≠ 0), neg_zero,
      Flow.map_zero_apply, hzero])
  have hu : Real.sqrt (-r) ∈ Ioo (-a) a := by
    constructor
    · linarith [Real.sqrt_nonneg (-r)]
    · exact Real.sqrt_lt_sqrt (neg_nonneg.mpr hr.2) (by linarith [hr.1])
  have hur : -(Real.sqrt (-r)) ^ 2 = r := by rw [Real.sq_sqrt (neg_nonneg.mpr hr.2)]; ring
  simpa only [γ, γ', hur, ← C.end_flow] using heq hu

end Completion
end FsFltz.Geometry
