import FsFltz.Geometry.IntrinsicZeroLiouvilleDomain
import FsFltz.Geometry.CylindricalCompletion

/-!
# Witnessed rank-one pairs with arbitrary native zero-dimensional ribbons

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, especially the
finite zero-dimensional ribbon and its full core at lines 159–160; `sec:lean`,
lines 783–814 and 825–830. A compact native zero-dimensional source and a
prescribed injective map into the boundary of a Liouville surface construct
an actual witnessed pair. Native charts prove smoothness of the ribbon map;
compactness and injectivity give its topological embedding, and zero tangent
spaces give immersion. Its primitive compatibility is proved algebraically.

Both completions are constructed by existing foundations. The ambient
localization retains the original boundary and witness, and the ribbon map
is literally the original map under the native carrier inclusion. The full
embedded core is its entire image. No far-fiber construction or geometric
endpoint comparison is asserted.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry.IntrinsicZeroLiouville
open SmoothManifold

variable {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (Model 0) M] [IsManifold 𝓘(ℝ, Model 0) ∞ M]

/-- An arbitrary injective native zero-dimensional ribbon map is a smooth
embedding on the actual carrier extension used by its completion. -/
def ribbonEmbedding (D : LiouvilleDomain 2) (j : M → D.domain.boundary.Point)
    (hj : Function.Injective j) :
    (completion (M := M) 0).ambient.manifold.SmoothEmbedding D.domain.boundary := by
  let := source_discreteTopology M
  let := (completion (M := M) 0).ambient.manifold.discreteTopology_of_dimension_zero
  have hjs : ContMDiff 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 1) ∞ j :=
    contMDiff_of_discreteTopology
  have hjemb : Topology.IsEmbedding j := (hjs.continuous.isClosedEmbedding hj).isEmbedding
  exact
    { map := ⟨fun x => j x.val, contMDiff_of_discreteTopology⟩
      embedding := hjemb.comp Topology.IsEmbedding.subtypeVal
      immersion := fun _ => fun _ _ _ => PiLp.ext (fun i => Fin.elim0 i) }

/-- The prescribed zero-dimensional ribbon and positive boundary witness
produce an actual rank-one pair, with both completions constructed rather
than assumed. Its ambient has the original compact domain and boundary under
the native localization, and its ribbon primitive is the zero form. -/
def witnessedPair (D : LiouvilleDomain 2) (j : M → D.domain.boundary.Point)
    (hj : Function.Injective j) (b : D.domain.boundary.Point → ℝ)
    (hb : ContMDiff 𝓘(ℝ, Model 1) 𝓘(ℝ, ℝ) ∞ b)
    (hpositive : ∀ x, 0 < b x) : WitnessedPair 1 where
  ambientDomain := D.flowCollar.localizedDomain
  ribbonDomain := (liouvilleDomain M 0).carrierRestriction_of_dimension_zero
  ribbonEmbedding := ribbonEmbedding D j hj
  witness := b
  smooth_witness := hb
  positive_witness := hpositive
  ribbon_primitive := by
    intro x _
    change (completion (M := M) 0).ambient.manifold.pullback
      D.flowCollar.localizedDomain.domain.boundary (ribbonEmbedding D j hj).map
      (fun y => b y • D.flowCollar.localizedDomain.domain.boundaryForm
        D.flowCollar.localizedDomain.liouville.primitive y) x =
      (liouvilleDomain M 0).carrierRestriction_of_dimension_zero.liouville.primitive x
    have hz := (completion (M := M) 0).ambient.manifold.oneForm_eq_zero_of_dimension_zero
      ((completion (M := M) 0).ambient.manifold.pullback
        D.flowCollar.localizedDomain.domain.boundary (ribbonEmbedding D j hj).map
        (fun y => b y • D.flowCollar.localizedDomain.domain.boundaryForm
          D.flowCollar.localizedDomain.liouville.primitive y))
    rw [congrFun hz x]
    rw [(liouvilleDomain M 0).carrierRestriction_primitive_of_dimension_zero]
    rfl
  ambientCompletion := D.cylindricalCompletion
  ribbonCompletion := completion 0

variable (D : LiouvilleDomain 2) (j : M → D.domain.boundary.Point)
  (hj : Function.Injective j) (b : D.domain.boundary.Point → ℝ)
  (hb : ContMDiff 𝓘(ℝ, Model 1) 𝓘(ℝ, ℝ) ∞ b)
  (hpositive : ∀ x, 0 < b x)

/-- The actual pair's boundary ribbon map is the prescribed map under the
literal native carrier inclusion. -/
@[simp] theorem witnessedPair_ribbonEmbedding
    (x : (completion (M := M) 0).ambient.manifold.Point) :
    (witnessedPair D j hj b hb hpositive).ribbonEmbedding.map x = j x.val := rfl

/-- The native source equivalence commutes with the prescribed ribbon map. -/
@[simp] theorem witnessedPair_ribbonEmbedding_native (x : M) :
    (witnessedPair D j hj b hb hpositive).ribbonEmbedding.map
      (completionDiffeomorph 0 x) = j x := rfl

/-- Localization retains the original positive witness literally. -/
@[simp] theorem witnessedPair_witness :
    (witnessedPair D j hj b hb hpositive).witness = b := rfl

/-- The full embedded core of this actual constructed pair is the entire
prescribed native ribbon image. -/
theorem witnessedPair_embeddedCore :
    (witnessedPair D j hj b hb hpositive).embeddedCore = range j := by
  exact image_embedded_completion_core (0 : (sourceManifold M).Form 1) j

end FsFltz.Geometry.IntrinsicZeroLiouville
