import FsFltz.Geometry.SmoothScalarExtension
import FsFltz.Geometry.Family

/-!
# Joint scalar germs for witnesses on an actual fixed boundary

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–160;
`def:chain`, lines 163–169; and `sec:lean`, lines 788–814.
On the original boundary manifold, scalar germs around each interval point
glue to a real-time smooth extension. The resulting interval family retains
every prescribed value, so any positivity assertion on the interval is
unchanged. The germs need not agree away from the interval, and neither
off-interval positivity nor a prechosen global extension is required.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.SmoothManifold

variable {d : ℕ} (M : SmoothManifold d)

/-- Joint smooth extension germs on the actual manifold, including both
parameter endpoints. Agreement is required only at interval times. -/
def IsLocallyExtendibleIntervalScalarFamily
    (b : Parameter → M.Point → ℝ) : Prop :=
  ∀ (t : Parameter) (x : M.Point),
    ∃ (U : Set (ℝ × M.Point)) (g : ℝ × M.Point → ℝ),
      IsOpen U ∧ (t.val, x) ∈ U ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, ℝ) ∞ g U ∧
      ∀ (s : Parameter) (y : M.Point), (s.val, y) ∈ U → g (s.val, y) = b s y

/-- Global joint manifold smoothness gives the chart coefficient regularity
used by the family API. -/
theorem isSmoothScalarFamily_of_contMDiff
    {b : ℝ → M.Point → ℝ}
    (hb : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M.Point => b p.1 p.2)) :
    M.IsSmoothScalarFamily b := by
  intro x
  let c := chartAt (Model d) x
  refine ⟨univ ×ˢ c.target, isOpen_univ.prod c.open_target,
    prod_mono (subset_univ _) Subset.rfl, ?_⟩
  have hc : ContMDiffOn 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ c.symm c.target :=
    contMDiffOn_chart_symm
  intro p hp
  have he := hc.contMDiffAt (c.open_target.mem_nhds hp.2)
  have hq : ContMDiffAt 𝓘(ℝ, ℝ × Model d)
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d)) ∞
      (fun p : ℝ × Model d => (p.1, c.symm p.2)) p :=
    contDiff_fst.contMDiff.contMDiffAt.prodMk
      (he.comp p contDiff_snd.contMDiff.contMDiffAt)
  exact ((hb _).comp p hq).contDiffAt.contDiffWithinAt

/-- Partition of unity on the real-time product glues the supplied local
germs, with exact agreement at every interval point. -/
theorem isSmoothIntervalScalarFamily_of_local_germs
    (b : Parameter → M.Point → ℝ)
    (hb : M.IsLocallyExtendibleIntervalScalarFamily b) :
    M.IsSmoothIntervalScalarFamily b := by
  classical
  let A : Set (ℝ × M.Point) := parameterInterval ×ˢ univ
  let f : ℝ × M.Point → ℝ := fun p =>
    if hp : p.1 ∈ parameterInterval then b ⟨p.1, hp⟩ p.2 else 0
  have hA : IsClosed A := isClosed_Icc.prod isClosed_univ
  let : ChartedSpace (ℝ × Model d) (ℝ × M.Point) :=
    prodChartedSpace ℝ ℝ (Model d) M.Point
  let : IsManifold 𝓘(ℝ, ℝ × Model d) ∞ (ℝ × M.Point) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod ℝ M.Point
  have hlocal : ∀ p ∈ A, ∃ U ∈ 𝓝 p, ∃ g : ℝ × M.Point → ℝ,
      ContMDiffOn 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, ℝ) ∞ g U ∧ EqOn g f (U ∩ A) := by
    intro p hp
    obtain ⟨U, g, hU, hpU, hg, heq⟩ := hb ⟨p.1, hp.1⟩ p.2
    refine ⟨U, hU.mem_nhds hpU, g, ?_, ?_⟩
    · rw [modelWithCornersSelf_prod]
      exact hg
    · intro q hq
      simpa only [f, dite_eq_left hq.2.1] using heq ⟨q.1, hq.2.1⟩ q.2 hq.1
  obtain ⟨g, hg, heq⟩ := exists_contMDiff_scalarExtension_of_closed hA hlocal
  refine ⟨fun t x => g (t, x), ?_, ?_⟩
  · apply M.isSmoothScalarFamily_of_contMDiff
    rw [← modelWithCornersSelf_prod]
    exact hg
  · intro t
    funext x
    have ht : t.val ∈ parameterInterval := t.property
    simpa only [f, dite_eq_left ht] using
      heq (show (t.val, x) ∈ A from ⟨t.property, mem_univ x⟩)

end FsFltz.Geometry.SmoothManifold
