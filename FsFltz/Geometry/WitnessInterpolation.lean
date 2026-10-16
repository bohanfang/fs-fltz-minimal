import FsFltz.Geometry.OriginalParameterPairFamily
import FsFltz.Geometry.IntrinsicBoundaryWitnessFamily
import FsFltz.Geometry.MaslovClassPullback

/-!
# Positive boundary witness interpolation on the same completed pair

Source: `geometric-part-fsf-proof.tex`, `subsec:junction`, lines 1908–1919;
`geoemtric-part-fsf.tex`, `def:chain`, lines 163–199. Agreement on the
whole compact ribbon fixes its primitive pointwise. Both given completions
and their fields are retained, rather than chosen again.
-/

noncomputable section
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry
open SmoothManifold
set_option backward.isDefEq.respectTransparency false

namespace WitnessedPair

variable {n : ℕ} (P : WitnessedPair n)

/-- Change only the positive boundary witness, keeping its entire ribbon
restriction, the actual primitive, and both given completions. -/
def withWitness (b : P.ambientDomain.domain.boundary.Point → ℝ)
    (hb : ContMDiff 𝓘(ℝ, Model (2 * n - 1)) 𝓘(ℝ, ℝ) ∞ b)
    (hpos : ∀ x, 0 < b x)
    (heq : ∀ x ∈ P.ribbonDomain.domain.carrier,
      b (P.ribbonEmbedding.map x) = P.witness (P.ribbonEmbedding.map x)) : WitnessedPair n :=
  { P with
    witness := b
    smooth_witness := hb
    positive_witness := hpos
    ribbon_primitive := by
      intro x hx
      rw [← P.ribbon_primitive x hx]
      unfold SmoothManifold.pullback
      dsimp only
      rw [heq x hx] }

theorem withWitness_eq_self (b : P.ambientDomain.domain.boundary.Point → ℝ)
    (hb : ContMDiff 𝓘(ℝ, Model (2 * n - 1)) 𝓘(ℝ, ℝ) ∞ b)
    (hpos : ∀ x, 0 < b x)
    (heq : ∀ x ∈ P.ribbonDomain.domain.carrier,
      b (P.ribbonEmbedding.map x) = P.witness (P.ribbonEmbedding.map x))
    (hw : b = P.witness) : P.withWitness b hb hpos heq = P := by
  subst b
  rfl

theorem withWitness_congr (b c : P.ambientDomain.domain.boundary.Point → ℝ)
    (hb : ContMDiff 𝓘(ℝ, Model (2 * n - 1)) 𝓘(ℝ, ℝ) ∞ b)
    (hc : ContMDiff 𝓘(ℝ, Model (2 * n - 1)) 𝓘(ℝ, ℝ) ∞ c)
    (hposb : ∀ x, 0 < b x) (hposc : ∀ x, 0 < c x)
    (heqb : ∀ x ∈ P.ribbonDomain.domain.carrier,
      b (P.ribbonEmbedding.map x) = P.witness (P.ribbonEmbedding.map x))
    (heqc : ∀ x ∈ P.ribbonDomain.domain.carrier,
      c (P.ribbonEmbedding.map x) = P.witness (P.ribbonEmbedding.map x))
    (hbc : b = c) : P.withWitness b hb hposb heqb = P.withWitness c hc hposc heqc := by
  subst c
  rfl

@[simp] theorem withWitness_embeddedCore
    (b : P.ambientDomain.domain.boundary.Point → ℝ)
    (hb : ContMDiff 𝓘(ℝ, Model (2 * n - 1)) 𝓘(ℝ, ℝ) ∞ b)
    (hpos : ∀ x, 0 < b x)
    (heq : ∀ x ∈ P.ribbonDomain.domain.carrier,
      b (P.ribbonEmbedding.map x) = P.witness (P.ribbonEmbedding.map x)) :
    (P.withWitness b hb hpos heq).embeddedCore = P.embeddedCore := rfl

/-- Logarithmic interpolation of the two globally positive witnesses. -/
def interpolatedWitness (b : P.ambientDomain.domain.boundary.Point → ℝ)
    (t : ℝ) (x : P.ambientDomain.domain.boundary.Point) : ℝ :=
  Real.exp ((1 - t) * Real.log (P.witness x) + t * Real.log (b x))

@[simp] theorem interpolatedWitness_zero (b : P.ambientDomain.domain.boundary.Point → ℝ) :
    P.interpolatedWitness b 0 = P.witness := by
  funext x
  simp [interpolatedWitness, Real.exp_log (P.positive_witness x)]

@[simp] theorem interpolatedWitness_one (b : P.ambientDomain.domain.boundary.Point → ℝ)
    (hpos : ∀ x, 0 < b x) : P.interpolatedWitness b 1 = b := by
  funext x
  simp [interpolatedWitness, Real.exp_log (hpos x)]

theorem interpolatedWitness_eq_on_ribbon
    (b : P.ambientDomain.domain.boundary.Point → ℝ)
    (heq : ∀ x ∈ P.ribbonDomain.domain.carrier,
      b (P.ribbonEmbedding.map x) = P.witness (P.ribbonEmbedding.map x))
    (t : ℝ) (x : P.ribbonDomain.domain.extension.Point)
    (hx : x ∈ P.ribbonDomain.domain.carrier) :
    P.interpolatedWitness b t (P.ribbonEmbedding.map x) =
      P.witness (P.ribbonEmbedding.map x) := by
  unfold interpolatedWitness
  rw [heq x hx]
  convert Real.exp_log (P.positive_witness (P.ribbonEmbedding.map x)) using 1
  congr 1
  ring

theorem contMDiff_interpolatedWitness
    (b : P.ambientDomain.domain.boundary.Point → ℝ)
    (hb : ContMDiff 𝓘(ℝ, Model (2 * n - 1)) 𝓘(ℝ, ℝ) ∞ b)
    (hpos : ∀ x, 0 < b x) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n - 1))) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × P.ambientDomain.domain.boundary.Point =>
        P.interpolatedWitness b p.1 p.2) := by
  have hlogb : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n - 1)))
      𝓘(ℝ, ℝ) ∞ (fun p : ℝ × P.ambientDomain.domain.boundary.Point => Real.log (b p.2)) :=
    fun p => (Real.contDiffAt_log.mpr (ne_of_gt (hpos p.2))).contMDiffAt.comp p
      ((hb.comp contMDiff_snd) p)
  have hlogw : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n - 1)))
      𝓘(ℝ, ℝ) ∞ (fun p : ℝ × P.ambientDomain.domain.boundary.Point => Real.log (P.witness p.2)) :=
    fun p => (Real.contDiffAt_log.mpr (ne_of_gt (P.positive_witness p.2))).contMDiffAt.comp p
      ((P.smooth_witness.comp contMDiff_snd) p)
  exact Real.contDiff_exp.contMDiff.comp
    (((contMDiff_const.sub contMDiff_fst).mul hlogw).add (contMDiff_fst.mul hlogb))

/-- The only varying datum is the explicit positive witness. Every compact
and completed presentation is the identity, and the entire ribbon primitive
is fixed. -/
def witnessDeformation
    (b : P.ambientDomain.domain.boundary.Point → ℝ)
    (hb : ContMDiff 𝓘(ℝ, Model (2 * n - 1)) 𝓘(ℝ, ℝ) ∞ b)
    (hpos : ∀ x, 0 < b x)
    (heq : ∀ x ∈ P.ribbonDomain.domain.carrier,
      b (P.ribbonEmbedding.map x) = P.witness (P.ribbonEmbedding.map x)) :
    PairDeformation n := by
  let bs := fun t : Parameter => P.interpolatedWitness b t.val
  have hbs : P.ambientDomain.domain.boundary.IsSmoothIntervalScalarFamily bs :=
    ⟨P.interpolatedWitness b,
      P.ambientDomain.domain.boundary.isSmoothScalarFamily_of_contMDiff
        (P.contMDiff_interpolatedWitness b hb hpos), fun _ => rfl⟩
  let Q := fun t : Parameter => P.withWitness (bs t) (hbs.contMDiff_slice t)
    (fun _ => Real.exp_pos _) (P.interpolatedWitness_eq_on_ribbon b heq t.val)
  let a := DomainPresentationEquiv.refl P.ambientDomain.domain
  let f := DomainPresentationEquiv.refl P.ribbonDomain.domain
  let ac : CompletionPresentationEquiv P.ambientCompletion P.ambientCompletion a :=
    { equiv := Diffeomorph.refl _ _ ∞
      compact_square := fun _ _ => rfl
      end_square := fun _ _ _ => rfl }
  let fc : CompletionPresentationEquiv P.ribbonCompletion P.ribbonCompletion f :=
    { equiv := Diffeomorph.refl _ _ ∞
      compact_square := fun _ _ => rfl
      end_square := fun _ _ _ => rfl }
  refine
    { pair := Q
      ambientPresentation := fun _ => a
      ribbonPresentation := fun _ => f
      ambientCompletionPresentation := fun _ => ac
      ribbonCompletionPresentation := fun _ => fc
      ambientPrimitive_smooth := ?_
      ribbonPrimitive_smooth := ?_
      ambientField_smooth := ?_
      ribbonField_smooth := ?_
      ribbonEmbedding_smooth := ?_
      witness_smooth := hbs
      completedAmbientPrimitive_smooth := ?_
      completedRibbonPrimitive_smooth := ?_
      completedAmbientField_smooth := ?_
      completedRibbonField_smooth := ?_ }
  · change P.ambientDomain.domain.extension.IsSmoothIntervalFormFamily
      (fun _ => P.ambientDomain.domain.extension.pullback _ id P.ambientDomain.liouville.primitive)
    rw [P.ambientDomain.domain.extension.pullback_id]
    exact P.ambientDomain.domain.extension.isSmoothIntervalFormFamily_constant _
      P.ambientDomain.liouville.smooth_primitive
  · change P.ribbonDomain.domain.extension.IsSmoothIntervalFormFamily
      (fun _ => P.ribbonDomain.domain.extension.pullback _ id P.ribbonDomain.liouville.primitive)
    rw [P.ribbonDomain.domain.extension.pullback_id]
    exact P.ribbonDomain.domain.extension.isSmoothIntervalFormFamily_constant _
      P.ribbonDomain.liouville.smooth_primitive
  · change P.ambientDomain.domain.extension.IsSmoothIntervalVectorFieldFamily
      (fun _ => P.ambientDomain.domain.extension.pullbackVectorField _
        (Diffeomorph.refl _ _ ∞) P.ambientDomain.liouville.field)
    rw [P.ambientDomain.domain.extension.pullbackVectorField_refl]
    exact P.ambientDomain.domain.extension.isSmoothIntervalVectorFieldFamily_constant _
      P.ambientDomain.liouville.smooth_field
  · change P.ribbonDomain.domain.extension.IsSmoothIntervalVectorFieldFamily
      (fun _ => P.ribbonDomain.domain.extension.pullbackVectorField _
        (Diffeomorph.refl _ _ ∞) P.ribbonDomain.liouville.field)
    rw [P.ribbonDomain.domain.extension.pullbackVectorField_refl]
    exact P.ribbonDomain.domain.extension.isSmoothIntervalVectorFieldFamily_constant _
      P.ribbonDomain.liouville.smooth_field
  · exact P.ribbonDomain.domain.extension.isSmoothIntervalMapFamily_constant _ _
      P.ribbonEmbedding.map.contMDiff
  · change P.ambientManifold.IsSmoothIntervalFormFamily
      (fun _ => P.ambientManifold.pullback _ id P.ambientCompletion.ambient.primitive)
    rw [P.ambientManifold.pullback_id]
    exact P.ambientManifold.isSmoothIntervalFormFamily_constant _
      P.ambientCompletion.ambient.smooth_primitive
  · change P.ribbonCompletion.ambient.manifold.IsSmoothIntervalFormFamily
      (fun _ => P.ribbonCompletion.ambient.manifold.pullback _ id
        P.ribbonCompletion.ambient.primitive)
    rw [P.ribbonCompletion.ambient.manifold.pullback_id]
    exact P.ribbonCompletion.ambient.manifold.isSmoothIntervalFormFamily_constant _
      P.ribbonCompletion.ambient.smooth_primitive
  · change P.ambientManifold.IsSmoothIntervalVectorFieldFamily
      (fun _ => P.ambientManifold.pullbackVectorField _
        (Diffeomorph.refl _ _ ∞) P.ambientCompletion.ambient.field)
    rw [P.ambientManifold.pullbackVectorField_refl]
    exact P.ambientManifold.isSmoothIntervalVectorFieldFamily_constant _
      P.ambientCompletion.ambient.smooth_field
  · change P.ribbonCompletion.ambient.manifold.IsSmoothIntervalVectorFieldFamily
      (fun _ => P.ribbonCompletion.ambient.manifold.pullbackVectorField _
        (Diffeomorph.refl _ _ ∞) P.ribbonCompletion.ambient.field)
    rw [P.ribbonCompletion.ambient.manifold.pullbackVectorField_refl]
    exact P.ribbonCompletion.ambient.manifold.isSmoothIntervalVectorFieldFamily_constant _
      P.ribbonCompletion.ambient.smooth_field

@[simp] theorem witnessDeformation_source
    (b : P.ambientDomain.domain.boundary.Point → ℝ)
    (hb : ContMDiff 𝓘(ℝ, Model (2 * n - 1)) 𝓘(ℝ, ℝ) ∞ b)
    (hpos : ∀ x, 0 < b x)
    (heq : ∀ x ∈ P.ribbonDomain.domain.carrier,
      b (P.ribbonEmbedding.map x) = P.witness (P.ribbonEmbedding.map x)) :
    (P.witnessDeformation b hb hpos heq).source = P := by
  exact P.withWitness_eq_self _ _ _ (P.interpolatedWitness_eq_on_ribbon b heq 0)
    (P.interpolatedWitness_zero b)

@[simp] theorem witnessDeformation_target
    (b : P.ambientDomain.domain.boundary.Point → ℝ)
    (hb : ContMDiff 𝓘(ℝ, Model (2 * n - 1)) 𝓘(ℝ, ℝ) ∞ b)
    (hpos : ∀ x, 0 < b x)
    (heq : ∀ x ∈ P.ribbonDomain.domain.carrier,
      b (P.ribbonEmbedding.map x) = P.witness (P.ribbonEmbedding.map x)) :
    (P.witnessDeformation b hb hpos heq).target = P.withWitness b hb hpos heq := by
  exact P.withWitness_congr _ _ _ _ _ _ (P.interpolatedWitness_eq_on_ribbon b heq 1) heq
    (P.interpolatedWitness_one b hpos)

@[simp] theorem witnessDeformation_embeddedCore
    (b : P.ambientDomain.domain.boundary.Point → ℝ)
    (hb : ContMDiff 𝓘(ℝ, Model (2 * n - 1)) 𝓘(ℝ, ℝ) ∞ b)
    (hpos : ∀ x, 0 < b x)
    (heq : ∀ x ∈ P.ribbonDomain.domain.carrier,
      b (P.ribbonEmbedding.map x) = P.witness (P.ribbonEmbedding.map x))
    (t : Parameter) :
    ((P.witnessDeformation b hb hpos heq).pair t).embeddedCore = P.embeddedCore := rfl

/-- This very witness deformation carries any ambient datum constantly.
The two completion presentations are identities, so the lift agrees
literally at both junctions. -/
def gradedWitnessDeformation
    (b : P.ambientDomain.domain.boundary.Point → ℝ)
    (hb : ContMDiff 𝓘(ℝ, Model (2 * n - 1)) 𝓘(ℝ, ℝ) ∞ b)
    (hpos : ∀ x, 0 < b x)
    (heq : ∀ x ∈ P.ribbonDomain.domain.carrier,
      b (P.ribbonEmbedding.map x) = P.witness (P.ribbonEmbedding.map x))
    (datum : P.Maslov) :
    GradedPairDeformation (P.witnessDeformation b hb hpos heq) datum datum where
  etaExtension := fun _ => P.ambientSymplecticForm
  eta_agrees := by
    intro t
    change P.ambientSymplecticForm = P.ambientManifold.exteriorDerivative
      (P.ambientManifold.pullback _ id P.ambientCompletion.ambient.primitive)
    rw [P.ambientManifold.pullback_id]
    rfl
  family := (MaslovHomotopy.refl datum).family
  sourceJ := (pullbackAlmostComplex_refl P.ambientManifold datum.J).symm
  targetJ := (pullbackAlmostComplex_refl P.ambientManifold datum.J).symm
  sourceTensor := (pullbackSquaredTensor_refl P.ambientManifold datum.tensor).symm
  targetTensor := (pullbackSquaredTensor_refl P.ambientManifold datum.tensor).symm

end WitnessedPair
end FsFltz.Geometry
