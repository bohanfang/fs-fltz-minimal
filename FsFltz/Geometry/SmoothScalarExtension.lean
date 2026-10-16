import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Smooth scalar extension from a closed carrier

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and
`sec:lean`, lines 783–814. Smooth scalar data on the native compact piece
must extend on the same boundaryless presentation. Partition of unity
patches germs which match on the carrier; they need not agree elsewhere.
The extension theorem assumes local germs and produces the global function.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace B] [ChartedSpace E B]
  [IsManifold 𝓘(ℝ, E) ∞ B] [T2Space B] [SecondCountableTopology B]

/-- Matching smooth scalar germs on a closed carrier give a global smooth
extension with exactly the prescribed values on that carrier. Compact
carriers are covered by `IsCompact.isClosed`; no uniform germ radius or
agreement between germs outside the carrier is required. -/
theorem exists_contMDiff_scalarExtension_of_closed
    {A : Set B} (hA : IsClosed A) {f : B → ℝ}
    (hlocal : ∀ x ∈ A, ∃ U ∈ 𝓝 x, ∃ g : B → ℝ,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U ∧ EqOn g f (U ∩ A)) :
    ∃ g : B → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ EqOn g f A := by
  classical
  let : LocallyCompactSpace B := ChartedSpace.locallyCompactSpace E B
  let : SigmaCompactSpace B := sigmaCompactSpace_of_locallyCompact_secondCountable
  let T : B → Set ℝ := fun x => if x ∈ A then {f x} else univ
  have hconv : ∀ x, Convex ℝ (T x) := by
    intro x
    by_cases hx : x ∈ A
    · simpa only [T, ite_eq_left hx] using convex_singleton (f x)
    · simpa only [T, ite_eq_right hx] using (convex_univ : Convex ℝ (univ : Set ℝ))
  have hloc : ∀ x : B, ∃ U ∈ 𝓝 x, ∃ g : B → ℝ,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U ∧ ∀ y ∈ U, g y ∈ T y := by
    intro x
    by_cases hx : x ∈ A
    · obtain ⟨U, hU, g, hg, heq⟩ := hlocal x hx
      refine ⟨U, hU, g, hg, ?_⟩
      intro y hy
      by_cases hyA : y ∈ A
      · simpa only [T, ite_eq_left hyA, mem_singleton_iff] using heq ⟨hy, hyA⟩
      · simp only [T, ite_eq_right hyA, mem_univ]
    · refine ⟨Aᶜ, hA.isOpen_compl.mem_nhds hx, fun _ => 0, contMDiffOn_const, ?_⟩
      intro y hy
      simp only [T, ite_eq_right hy, mem_univ]
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local 𝓘(ℝ, E) hconv hloc
  refine ⟨g, g.contMDiff, ?_⟩
  intro x hx
  simpa only [T, ite_eq_left hx, mem_singleton_iff] using hg x

end FsFltz.Geometry
