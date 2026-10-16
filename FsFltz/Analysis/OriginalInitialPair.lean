import FsFltz.Analysis.OriginalRibbonEmbedding
import FsFltz.Analysis.OriginalRoundedAbsorption
import FsFltz.Analysis.OriginalFiniteType
import FsFltz.Analysis.OriginalRounding

/-!
# The actual initial witnessed pair and G1–G2

Source: `geoemtric-part-fsf.tex`, `thm:target`, `g:initial`, lines 352–384,
and `sec:lean`, lines 783–814; `geometric-part-fsf-proof.tex`,
`prop:allinitial`, lines 878–948. The constructed original ambient and full
fiber supply both actual inclusion-induced completion markings. Every
admissible rounding and every valid end-bound/level choice retains the
entire prescribed nonempty ribbon, whose witnessing factor is one.
The endpoint comparison, full-core equality and transported grading are
separate geometric conclusions and are not asserted here.
-/

noncomputable section
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry
open SmoothManifold

set_option backward.isDefEq.respectTransparency false

/-- Every valid set of original parameters and every admissible rounding
produces the exact initial-pair data: both literal compact images, the full
far fiber, its actual ribbon square, witness one, and both inclusion/flow
completion markings. -/
theorem nonempty_originalInitialPairData {n : ℕ} (I : ToricInput n)
    {Aamb R Afib K Aminus A : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K)
    (hfib : FiberEndBound I Aamb R Afib) (hlevels : Afib < Aminus)
    (m : RoundingChoice) (hadmiss : GeometricAdmissibleRounding I R K Aminus A m) :
    Nonempty (InitialPairData I R K Aminus A m) := by
  let E := originalRoundedLiouvilleDomain I hamb hR hset hK hfib hlevels m hadmiss
  let D := originalRibbonLiouvilleDomain I hamb hR hfib hlevels m hadmiss.1 hadmiss.2.1
  let F := originalFullFiberModel I hamb hR
  obtain ⟨j, hj, hp⟩ := exists_originalRibbonBoundaryEmbedding I hamb hR hfib hlevels m
    hadmiss.1 hadmiss.2.1 hset hK hadmiss
  let P : WitnessedPair n :=
    { ambientDomain := E
      ribbonDomain := D
      ribbonEmbedding := j
      witness := fun _ => 1
      smooth_witness := contMDiff_const
      positive_witness := fun _ => zero_lt_one
      ribbon_primitive := by
        intro x _
        simpa only [one_smul] using congrFun hp x
      ambientCompletion := originalRoundedCompletion I hamb hR hset hK hfib hlevels m hadmiss
      ribbonCompletion := originalRibbonCompletion I hamb hR hfib hlevels m hadmiss.1 hadmiss.2.1 }
  let i : E.domain.extension.SmoothEmbedding (lgManifold n) :=
    { map := ContMDiffMap.id
      embedding := Topology.IsEmbedding.id
      immersion := by
        intro x
        change Function.Injective (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) id x)
        rw [mfderiv_id]
        exact Function.injective_id }
  exact ⟨{
    pair := P
    ambient := originalCompletePrimitive I
      ((zero_le_one.trans (one_le_K0 I R hset.1 hset.2)).trans hK)
    domainEmbedding := i
    domain_image := by
      change id '' RoundedDomain I R A m = RoundedDomain I R A m
      exact image_id _
    ambientMarking := originalRoundedInclusionMarking I hamb hR hset hK hfib hlevels m hadmiss
      (originalRoundedCompletion I hamb hR hset hK hfib hlevels m hadmiss)
    witness_one := fun _ => rfl
    fiber := F
    ribbonInFiber := originalRibbonInFiber I hamb hR hfib hlevels m hadmiss.1 hadmiss.2.1
    ribbon_image := originalRibbonLiouvilleDomain_image I hamb hR hfib hlevels m hadmiss.1 hadmiss.2.1
    ribbon_square := fun x _ => hj x
    fiberMarking := originalRibbonInclusionMarking I hamb hR hfib hlevels m hadmiss.1 hadmiss.2.1
    ribbon_nonempty := originalRibbonLiouvilleDomain_nonempty I hamb hR hfib hlevels m hadmiss.1 hadmiss.2.1 }⟩

end FsFltz.Geometry

namespace FsFltz

/-- G1–G2 follow from the finite toric input with the source's full
quantifier order: one common ambient bound/radius, every large radius,
every valid fiber bound, every allowed `K` and level pair, existence of a
rounding, and the exact initial-pair data for every admissible rounding.
No geometric chain, full-core equality or grading comparison is assumed. -/
theorem ToricInput.initialGeometricAssertions {n : ℕ} (I : ToricInput n) :
    InitialGeometricAssertions I := by
  refine ⟨I.allNonnegativeComplete, ?_⟩
  obtain ⟨Aamb, R0, hamb, hR0, hbounds⟩ := I.exists_initial_rounding_bounds
  refine ⟨Aamb, R0, hamb, hR0, ?_⟩
  intro R hR
  obtain ⟨hset, hfib, hround⟩ := hbounds R hR
  refine ⟨⟨hset.1, hset.2, hfib⟩, ?_⟩
  intro Afib hAfib K hK Aminus A hAminus hA
  refine ⟨hround Afib hAfib K hK Aminus hAminus A hA, ?_⟩
  intro m hm
  exact Geometry.nonempty_originalInitialPairData I hamb (hR0.trans_le hR)
    hset hK hAfib hAminus m hm

end FsFltz
