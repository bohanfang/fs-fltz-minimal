import FsFltz.Geometry.FamilyLiouvilleNeighborhood
import FsFltz.Geometry.CollarExtension

/-!
# Smooth extensions of compact Liouville family fields

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–169, and `sec:lean`,
lines 788–814. Smooth interval primitives on a fixed compact domain produce
replacement Liouville structures on that same domain with literally the same
primitives and the same fields on its carrier. Their extended fields are
jointly smooth for all real parameters. The original fields need not vary
smoothly outside the compact carrier.

The canonical contraction field is smooth on a common nondegeneracy
neighborhood of the compact parameter-times-domain seam. A compact smooth
cutoff equal to one near that seam extends it by zero. The extension is a
Liouville field on the compact domain; no contraction equation or
symplecticity is asserted outside that domain. This constructs no completion
and proves no geometric comparison chain.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry
namespace SmoothManifold

set_option backward.isDefEq.respectTransparency false in
/-- A globally jointly smooth native vector along the spatial projection has
the chartwise smooth family coefficients required by the interval API. -/
theorem isSmoothVectorFieldFamily_of_contMDiff_section {d : ℕ} (M : SmoothManifold d)
    (Z : (t : ℝ) → (x : M.Point) → M.Tangent x)
    (hZ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      (𝓘(ℝ, Model d)).tangent ∞
      (fun p : ℝ × M.Point =>
        (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point))) :
    M.IsSmoothVectorFieldFamily Z := by
  intro a
  let c := chartAt (Model d) a
  let e := trivializationAt (Model d) (TangentSpace (𝓘(ℝ, Model d))) a
  refine ⟨univ ×ˢ c.target, isOpen_univ.prod c.open_target,
    prod_mono (subset_univ _) Subset.rfl, ?_⟩
  intro p hp
  have hx := c.map_target hp.2
  have he : (⟨c.symm p.2, Z p.1 (c.symm p.2)⟩ :
      TangentBundle 𝓘(ℝ, Model d) M.Point) ∈ e.source := hx
  have hc : ContMDiffAt 𝓘(ℝ, ℝ × Model d)
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
      (fun q : ℝ × Model d => (q.1, c.symm q.2)) p :=
    contDiffAt_fst.contMDiffAt.prodMk
      (((contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d)) (n := ∞) (x := a)).contMDiffAt
        (c.open_target.mem_nhds hp.2)).comp p contDiffAt_snd.contMDiffAt)
  have hcoeff := (e.contMDiffAt_iff
    (f := fun q : ℝ × M.Point =>
      (⟨q.2, Z q.1 q.2⟩ : TangentBundle 𝓘(ℝ, Model d) M.Point))
    (IM := (𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
    (IB := 𝓘(ℝ, Model d)) he).mp (hZ (p.1, c.symm p.2)) |>.2
  apply ((hcoeff.comp p hc).contDiffAt.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
    (c.open_target.mem_nhds hp.2)] with q hq
  dsimp only [Function.comp_def, vectorInChart]
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem
    (R := ℝ) e (c.map_target hq)]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt (c.map_target hq)]
  rfl

end SmoothManifold

namespace CompactDomain

set_option backward.isDefEq.respectTransparency false in
/-- Replace arbitrary off-carrier extensions of a compact Liouville family
by fields that are jointly smooth for all real parameters. The domain and
primitives are unchanged, and the actual fields agree everywhere on the
compact carrier, so contraction and strict outwardness are preserved. -/
theorem exists_liouvilleFamily_smoothFieldReplacement {d : ℕ} (D : CompactDomain d)
    (L : Parameter → LiouvilleStructure D)
    (halpha : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive)) :
    ∃ L' : Parameter → LiouvilleStructure D,
      (∀ t, (L' t).primitive = (L t).primitive) ∧
      (∀ t x, x ∈ D.carrier → (L' t).field x = (L t).field x) ∧
      D.extension.IsSmoothIntervalVectorFieldFamily (fun t => (L' t).field) ∧
      ∃ Z : (t : ℝ) → (x : D.extension.Point) → D.extension.Tangent x,
        ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
          (𝓘(ℝ, Model d)).tangent ∞
          (fun p : ℝ × D.extension.Point =>
            (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) D.extension.Point)) ∧
        ∀ t : Parameter, Z t.val = (L' t).field := by
  obtain ⟨alpha, _, _, Ω, hseam, _, _, hcanonical, hagree⟩ :=
    D.exists_liouvilleFamily_nondegenerateNeighborhood L halpha
  let : LocallyCompactSpace (ModelProd ℝ (Model d)) :=
    inferInstanceAs (LocallyCompactSpace (ℝ × Model d))
  obtain ⟨χ, V, hχ, hKV, hone, _, hsupp⟩ :=
    CollarExtension.exists_smooth_compact_cutoff
      (I := (𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((show IsCompact parameterInterval from isCompact_Icc).prod D.compact)
      Ω.isOpen hseam
  let v : (p : ℝ × D.extension.Point) →
      TangentSpace ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) p :=
    fun p => (0, D.extension.liouvilleVector (alpha p.1) p.2)
  have hv : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      (((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)).tangent) ∞
      (fun p => (⟨p, v p⟩ :
        TangentBundle ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (ℝ × D.extension.Point))) Ω := by
    have ht : ContMDiff 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).tangent) ∞
        (fun t : ℝ => (⟨t, (0 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
      contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
    exact contMDiff_equivTangentBundleProd_symm.comp_contMDiffOn
      ((ht.comp contMDiff_fst).contMDiffOn.prodMk hcanonical)
  let Z := fun t x => χ (t, x) • D.extension.liouvilleVector (alpha t) x
  have hZ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      (𝓘(ℝ, Model d)).tangent ∞
      (fun p : ℝ × D.extension.Point =>
        (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) D.extension.Point)) :=
    (contMDiff_equivTangentBundleProd.comp
      (hχ.contMDiffOn.smul_section_of_tsupport Ω.isOpen hsupp hv)).snd
  have heq : ∀ t : Parameter, ∀ x ∈ D.carrier, Z t.val x = (L t).field x := by
    intro t x hx
    dsimp only [Z]
    rw [hone (t.val, x) (hKV (show (t.val, x) ∈ parameterInterval ×ˢ D.carrier from
      ⟨t.property, hx⟩)), one_smul, hagree t x hx]
  let L' : Parameter → LiouvilleStructure D := fun t =>
    { primitive := (L t).primitive
      smooth_primitive := (L t).smooth_primitive
      symplectic := (L t).symplectic
      field := Z t.val
      smooth_field := D.extension.isSmoothVectorField_of_contMDiff_section
        (hZ.comp (contMDiff_const.prodMk contMDiff_id))
      contraction := fun x hx => by
        rw [heq t x hx]
        exact (L t).contraction x hx
      outward := fun x hx => by
        rw [heq t x (D.compact.isClosed.frontier_subset hx)]
        exact (L t).outward x hx }
  exact ⟨L', fun _ => rfl, heq,
    ⟨Z, D.extension.isSmoothVectorFieldFamily_of_contMDiff_section Z hZ, fun _ => rfl⟩,
    Z, hZ, fun _ => rfl⟩

end CompactDomain
end FsFltz.Geometry
