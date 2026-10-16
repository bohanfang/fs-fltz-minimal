import FsFltz.Geometry.OriginalVaryingLevelChoice
import FsFltz.Geometry.OriginalKMarkedPrefixPresentation

/-!
# Every initial choice attached to the retained original prefix

Source: `geometric-part-fsf-proof.tex`, `lem:choices`, lines 950–973,
and `sec:assembly`, lines 2141–2167; `geoemtric-part-fsf.tex`,
`thm:target`, lines 352–435. The comparison is constructed for the
supplied pair, retaining the exact convenient endpoint representative.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology

namespace FsFltz
open Geometry Geometry.SmoothManifold

/-- Attach an arbitrary initial choice to the actual retained prefix.
Both fiber bounds and all initial presentations remain arbitrary. The
first four arrows carry the prescribed grading; the full eight-arrow
path retains the original holomorphic and tailoring endpoints literally. -/
theorem PotentialTailoringOriginalMarkedPrefix.exists_arbitrary_source_chain
    {n : ℕ} {I : ToricInput n} {φ : RealSpace n → ℝ}
    {β Cplus Aminus originalK K : ℝ} {m : RoundingChoice}
    (P : PotentialTailoringOriginalMarkedPrefix I φ β Cplus Aminus originalK K m)
    {Aamb Afib Afib' B E : ℝ} {p : RoundingChoice}
    (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < Real.exp β)
    (hset : RatioSetWellDefined I (Real.exp β))
    (hK : K0 I (Real.exp β) ≤ originalK)
    (hfib : FiberEndBound I Aamb (Real.exp β) Afib)
    (hfib' : FiberEndBound I Aamb (Real.exp β) Afib')
    (hB : Afib < B) (hAminus : Afib' < Aminus)
    (S : InitialPairData I (Real.exp β) originalK B E p) :
    ∃ C : InitialChoiceComparison S P.original,
      C.chain.length = 3 ∧ C.targetDatum = P.originalMaslov ∧
      (C.chain.comp P.original_chain).length = 4 ∧
      Nonempty (GradedComparisonChain S.pair (C.chain.comp P.original_chain)
        C.sourceDatum P.matchingMaslov) ∧
      (C.chain.comp P.chain).length = 8 ∧
      C.chain.comp P.chain =
        ((C.chain.comp P.original_chain).cons (.identification P.junction)).comp
          P.marked.chain := by
  have hmin : FiberEndBound I Aamb (Real.exp β) (min Afib Afib') := by
    rcases le_total Afib Afib' with h | h
    · simpa only [min_eq_left h] using hfib
    · simpa only [min_eq_right h] using hfib'
  obtain ⟨C, hlength, hdatum⟩ := exists_originalInitialChoiceComparison_to_datum I
    hamb hR hset hK hmin ((min_le_left _ _).trans_lt hB)
      ((min_le_right _ _).trans_lt hAminus) S P.original
      P.originalMaslov P.original_prescribed
  have gC : GradedComparisonChain S.pair C.chain C.sourceDatum P.originalMaslov := by
    rw [← hdatum]
    exact C.graded
  refine ⟨C, hlength, hdatum, ?_, ⟨gC.comp P.original_grading⟩, ?_, ?_⟩
  · simp [Quiver.Path.length_comp, hlength, P.original_length]
  · simp [Quiver.Path.length_comp, hlength]
  · simp only [PotentialTailoringOriginalMarkedPrefix.chain, ← Quiver.Path.comp_assoc,
      Quiver.Path.comp_cons]

end FsFltz
