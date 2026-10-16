import FsFltz.Geometry.IntrinsicZeroIdentificationFamily
import FsFltz.Geometry.IntrinsicZeroRibbonFamily
import FsFltz.Geometry.IntrinsicBoundaryWitnessFamily
import FsFltz.Geometry.SmoothMapFiniteExtension

/-!
# Zero-dimensional native pair families from local joint germs

Source: `geoemtric-part-fsf.tex`, conventions 119–122, `def:pair`,
132–160, `def:chain`, 163–169, and `sec:lean`, 788–797 and 825–830.
The original native zero-dimensional source has no spatial boundary.
Target-valued germs on open subsets of time times that source are glued
near the compact closed interval product. Thus the pair family producer
needs neither a preselected total-time ribbon map nor a preselected witness
extension. The supplied maps and witnesses are retained on the interval.
Their geometric inequalities are required only there.

The ambient compact presentation and its native Liouville structures are
fixed input. This does not construct a varying native ambient boundary
presentation or prove the geometric endpoint target.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicZeroLiouville
open SmoothManifold

variable {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (Model 0) M] [IsManifold 𝓘(ℝ, Model 0) ∞ M]

/-- Target-valued joint smooth germs on the actual native source. The open
domain of each germ extends through the parameter endpoint, and agreement
is required only at interval times. -/
def IsLocallyExtendibleRibbonMapFamily {d : ℕ} (N : SmoothManifold d)
    (j : Parameter → M → N.Point) : Prop :=
  ∀ (t : Parameter) (x : M),
    ∃ U : TopologicalSpace.Opens (ℝ × M), (t.val, x) ∈ U ∧ ∃ g : U → N.Point,
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model 0)) 𝓘(ℝ, Model d) ∞ g ∧
      ∀ (s : Parameter) (y : M) (h : (s.val, y) ∈ U), g ⟨(s.val, y), h⟩ = j s y

/-- Compact target-chart gluing constructs the actual joint interval map
extension. Its arbitrary values outside the constructed open neighborhood
are obtained pointwise from the given reference map, including for an empty
source and an empty target; no target inhabitant is assumed. -/
theorem ribbonMapFamily_smooth_of_local_germs {d : ℕ} (N : SmoothManifold d)
    (j : Parameter → M → N.Point) (hj : IsLocallyExtendibleRibbonMapFamily N j) :
    (sourceManifold M).IsSmoothIntervalMapFamily N j := by
  classical
  have hprod : IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model 0)) ∞ (ℝ × M) := inferInstance
  let : ChartedSpace (ℝ × Model 0) (ℝ × M) := prodChartedSpace ℝ ℝ (Model 0) M
  rw [← modelWithCornersSelf_prod] at hprod
  let : IsManifold 𝓘(ℝ, ℝ × Model 0) ∞ (ℝ × M) := hprod
  let A : Set (ℝ × M) := parameterInterval ×ˢ univ
  let f : A → N.Point := fun p => j ⟨p.val.1, p.property.1⟩ p.val.2
  have hlocal : ∀ p : A, ∃ U : TopologicalSpace.Opens (ℝ × M), p.val ∈ U ∧
      ∃ g : U → N.Point, ContMDiff 𝓘(ℝ, ℝ × Model 0) 𝓘(ℝ, Model d) ∞ g ∧
        ∀ q (hqU : q ∈ U) (hqA : q ∈ A), g ⟨q, hqU⟩ = f ⟨q, hqA⟩ := by
    intro p
    obtain ⟨U, hpU, g, hg, heq⟩ := hj ⟨p.val.1, p.property.1⟩ p.val.2
    refine ⟨U, hpU, g, ?_, ?_⟩
    · rw [modelWithCornersSelf_prod]
      exact hg
    · intro q hqU hqA
      exact heq ⟨q.1, hqA.1⟩ q.2 hqU
  obtain ⟨W, hW, g, hg, heq⟩ :=
    SmoothMapExtension.exists_smoothMapExtension_of_compact
      (isCompact_Icc.prod isCompact_univ) f hlocal
  rw [modelWithCornersSelf_prod] at hg
  let ext : ℝ → M → N.Point := fun s x =>
    if h : (s, x) ∈ W then g ⟨(s, x), h⟩ else j parameterZero x
  have hrestriction : (fun p : W => ext p.val.1 p.val.2) = g := by
    funext p
    simp only [ext, dite_eq_left p.property]
  refine ⟨ext, ⟨W, W.isOpen, hW, ?_⟩, ?_⟩
  · intro p hp
    apply ContMDiffAt.contMDiffWithinAt
    apply (contMDiffAt_subtype_iff
      (f := fun p : ℝ × M => ext p.1 p.2) (x := (⟨p, hp⟩ : W))).mp
    rw [hrestriction]
    exact hg ⟨p, hp⟩
  · intro t
    funext x
    have hp : (t.val, x) ∈ A := ⟨t.property, mem_univ x⟩
    have hpW : (t.val, x) ∈ W := hW hp
    change ext t.val x = j t x
    dsimp only [ext]
    rw [dite_eq_left hpW]
    exact heq (t.val, x) hpW hp

/-- Original local joint ribbon-map and witness germs construct a native
rank-one pair deformation on the fixed ambient presentation. This consumes
both germ-gluing producers and the completed pair-family producer, retaining
each parameter's entire prescribed embedded core. No total-time maps or
witness extensions are supplied by the caller. -/
theorem exists_native_zero_pairDeformation_of_local_germs_with_presentations
    (D : CompactDomain 2) (L : Parameter → LiouvilleStructure D)
    (hL : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive))
    (μ : Parameter → (sourceManifold M).Form 1)
    (j : Parameter → M → D.boundary.Point)
    (hj : ∀ t, Function.Injective (j t))
    (hjs : IsLocallyExtendibleRibbonMapFamily D.boundary j)
    (b : Parameter → D.boundary.Point → ℝ)
    (hb : D.boundary.IsLocallyExtendibleIntervalScalarFamily b)
    (hpositive : ∀ t x, 0 < b t x) :
    let hb' := D.boundary.isSmoothIntervalScalarFamily_of_local_germs b hb
    ∃ hjs : (sourceManifold M).IsSmoothIntervalMapFamily D.boundary j,
    ∃ hprimitive : ∀ t x, x ∈ (compactDomain M).carrier →
      (compactDomain M).extension.pullback D.boundary
        (nativeRibbonEmbedding D (j t) (hj t)).map
        (fun y => b t y • D.boundaryForm (L t).primitive y) x =
          ((liouvilleFamily μ) t).primitive x,
    ∃ (ambient : LocalizedCompletionFamily D L)
      (ribbon : LocalizedCompletionFamily (compactDomain M) (liouvilleFamily μ))
      (Q : PairDeformation 1),
      Q = D.localizedPairDeformation (n := 1) (compactDomain M) L (liouvilleFamily μ)
        (fun t => nativeRibbonEmbedding D (j t) (hj t)) b hL
        (primitiveFamily_smooth μ) hjs hb' hpositive ambient ribbon hprimitive ∧
      (Q.pair = fun t => localizedZeroWitnessedPair ⟨D, L t⟩ (μ t)
        (ambient.collars t) (ribbon.collars t) (j t) (hj t) (b t)
        (hb'.contMDiff_slice t) (hpositive t)) ∧
      ∀ t, (localizedZeroWitnessedPair ⟨D, L t⟩ (μ t)
        (ambient.collars t) (ribbon.collars t) (j t) (hj t) (b t)
        (hb'.contMDiff_slice t) (hpositive t)).embeddedCore = range (j t) := by
  refine ⟨ribbonMapFamily_smooth_of_local_germs D.boundary j hjs, ?_⟩
  exact exists_native_zero_pairDeformation_on_fixed_ambient_with_presentations D L hL μ j hj
    (ribbonMapFamily_smooth_of_local_germs D.boundary j hjs) b
    (D.boundary.isSmoothIntervalScalarFamily_of_local_germs b hb) hpositive


/-- Original local joint ribbon-map and witness germs construct a native
rank-one pair deformation on the fixed ambient presentation. This consumes
both germ-gluing producers and the completed pair-family producer, retaining
each parameter's entire prescribed embedded core. No total-time maps or
witness extensions are supplied by the caller. -/
theorem exists_native_zero_pairDeformation_of_local_germs
    (D : CompactDomain 2) (L : Parameter → LiouvilleStructure D)
    (hL : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive))
    (μ : Parameter → (sourceManifold M).Form 1)
    (j : Parameter → M → D.boundary.Point)
    (hj : ∀ t, Function.Injective (j t))
    (hjs : IsLocallyExtendibleRibbonMapFamily D.boundary j)
    (b : Parameter → D.boundary.Point → ℝ)
    (hb : D.boundary.IsLocallyExtendibleIntervalScalarFamily b)
    (hpositive : ∀ t x, 0 < b t x) :
    let hb' := D.boundary.isSmoothIntervalScalarFamily_of_local_germs b hb
    ∃ A : (t : Parameter) → LiouvilleDomain.FlowCollar (⟨D, L t⟩ : LiouvilleDomain 2),
      ∃ B : (t : Parameter) → LiouvilleDomain.FlowCollar (liouvilleDomain M (μ t)),
        ∃ Q : PairDeformation 1,
          (Q.pair = fun t => localizedZeroWitnessedPair ⟨D, L t⟩ (μ t)
            (A t) (B t) (j t) (hj t) (b t) (hb'.contMDiff_slice t) (hpositive t)) ∧
          ∀ t, (localizedZeroWitnessedPair ⟨D, L t⟩ (μ t) (A t) (B t)
            (j t) (hj t) (b t) (hb'.contMDiff_slice t) (hpositive t)).embeddedCore = range (j t) := by
  obtain ⟨hjs', hprimitive, ambient, ribbon, Q, hQdef, hQ, hcore⟩ :=
    exists_native_zero_pairDeformation_of_local_germs_with_presentations
      D L hL μ j hj hjs b hb hpositive
  exact ⟨ambient.collars, ribbon.collars, Q, hQ, hcore⟩


end FsFltz.Geometry.IntrinsicZeroLiouville
