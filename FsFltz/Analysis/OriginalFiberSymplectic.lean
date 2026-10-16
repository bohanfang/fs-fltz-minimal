import FsFltz.Geometry.SymplecticBridge
import FsFltz.Geometry.BoundaryNondegeneracy
import FsFltz.Analysis.OriginalFiberManifold

/-!
# Exact symplectic form on an actual original fiber realization

Source: `geoemtric-part-fsf.tex`, `g:initial`, lines 373–384, and
`sec:lean`, lines 783–814; `geometric-part-fsf-proof.tex`,
`lem:originalends`, lines 770–818, and `prop:allinitial`, lines 923–930.
An actual smooth embedding whose tangent image is the kernel of the native
differential of `W` inherits the nondegenerate differential of the literal
restricted primitive `lambda0Form`. The proof uses the established native
cover formulas and their Kähler positivity, not an assumed fiber primitive.
The fiber manifold and its complete intrinsic flow are separate producers.
-/

noncomputable section
open scoped Manifold ContDiff

namespace FsFltz

/-- Holomorphicity of the proved logarithmic differential preserves its
kernel under the standard complex structure. -/
theorem dW_complexStructureCoordinates {n : ℕ} (I : ToricInput n)
    (y : LGSpace n) (q : TangentCoordinates n) :
    dW I y (complexStructureCoordinates q) = Complex.I * dW I y q := by
  rw [dW_eq_evaluation, tangentComplexCoordinates_complexStructure,
    CoordinateGeometry.evaluation_complexStructure, dW_eq_evaluation]

/-- The canonical two-form is nondegenerate on the actual logarithmic
kernel of `dW`: its positive complex-structure pairing detects every vector.
No positive-dimensional assumption is required. -/
theorem omega0Coordinates_nondegenerate_on_dW_kernel {n : ℕ} (I : ToricInput n)
    (y : LGSpace n) (q : TangentCoordinates n) (hq : dW I y q = 0)
    (hzero : ∀ r, dW I y r = 0 → omega0Coordinates q r = 0) : q = 0 := by
  by_contra hne
  have hpos := omegaKCoordinates_complexStructure_pos I y (K := 0)
    (by norm_num) q hne
  have hJ : dW I y (complexStructureCoordinates q) = 0 := by
    rw [dW_complexStructureCoordinates, hq, mul_zero]
  have hz := hzero (complexStructureCoordinates q) hJ
  simp only [omegaKCoordinates, zero_mul, add_zero] at hpos
  exact (ne_of_gt hpos) hz

namespace Geometry
open SmoothManifold

/-- Restriction of the native ambient symplectic form to the native kernel
of `dW` is nondegenerate. The cover differential is bijective, so the
coordinate Kähler argument tests every actual tangent vector. -/
theorem nondegenerate_lambda0Form_on_W_kernel {n : ℕ} (I : ToricInput n)
    (y : (lgManifold n).Point) (v : (lgManifold n).Tangent y)
    (hv : complexDifferential (lgManifold n) (W I) y v = 0)
    (hzero : ∀ w, complexDifferential (lgManifold n) (W I) y w = 0 →
      evalTwo ((lgManifold n).exteriorDerivative (lambda0Form n)) y v w = 0) :
    v = 0 := by
  obtain ⟨x, rfl⟩ := lgCover_surjective n y
  obtain ⟨q, rfl⟩ := (lgCoverTangent_bijective x).2 v
  have hq : dW I (lgCover x) q = 0 := by
    simpa only [complexDifferential_W_lgCover] using hv
  have hqzero : q = 0 := omega0Coordinates_nondegenerate_on_dW_kernel I
    (lgCover x) q hq (fun r hr => by
      have hz := hzero (lgCoverTangent x r) (by
        simpa only [complexDifferential_W_lgCover] using hr)
      have hcover := exteriorDerivative_lambdaKForm_lgCover I 0 x q r
      simp only [lambdaKForm, zero_smul, add_zero,
        omegaKCoordinates, zero_mul] at hcover
      exact hcover.symm.trans hz)
  rw [hqzero, map_zero]

/-- An actual immersed fiber realization inherits nondegeneracy from the
canonical ambient form when its tangent image is the native kernel of `dW`.
The tangent-image equation is supplied by the regular-level construction. -/
theorem nondegenerate_pullback_lambda0Form_of_tangent_kernel {n d : ℕ}
    (I : ToricInput n) (N : SmoothManifold d)
    (j : N.SmoothEmbedding (lgManifold n)) (x : N.Point)
    (hkernel : (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model (2 * n))) j.map x).range =
      (complexDifferential (lgManifold n) (W I) (j.map x)).ker) :
    N.Nondegenerate (N.exteriorDerivative
      (N.pullback (lgManifold n) j.map (lambda0Form n))) x := by
  intro v hzero
  rw [N.exteriorDerivative_pullback (lgManifold n) j.map (lambda0Form n)
    (isSmoothForm_lambda0Form n)] at hzero
  let D := mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model (2 * n))) j.map x
  have hvker : complexDifferential (lgManifold n) (W I) (j.map x) (D v) = 0 := by
    have hv : D v ∈ D.range := ⟨v, rfl⟩
    rw [hkernel] at hv
    exact hv
  have hvzero : D v = 0 := nondegenerate_lambda0Form_on_W_kernel I (j.map x)
    (D v) hvker (fun w hw => by
      have hwmem : w ∈ D.range := by
        rw [hkernel]
        exact hw
      obtain ⟨u, hu⟩ := hwmem
      change D u = w at hu
      have hz := hzero u
      change ((lgManifold n).exteriorDerivative (lambda0Form n) (j.map x))
        (D ∘ ![v, u]) = 0 at hz
      have htuple : D ∘ ![v, u] = ![D v, D u] := by
        funext i
        fin_cases i <;> rfl
      rw [htuple, hu] at hz
      exact hz)
  exact j.immersion x (hvzero.trans D.map_zero.symm)

/-- The literal pullback of `lambda0` is exact symplectic on every actual
smooth realization of a level of `W` with the proved tangent-kernel equation.
Smoothness and closedness are consequences of the existing exterior calculus;
no restricted primitive, nondegeneracy, or flow is assumed. -/
theorem isSymplecticOn_pullback_lambda0Form_of_tangent_kernel {n d : ℕ}
    (I : ToricInput n) (N : SmoothManifold d)
    (j : N.SmoothEmbedding (lgManifold n))
    (hkernel : ∀ x, (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model (2 * n))) j.map x).range =
      (complexDifferential (lgManifold n) (W I) (j.map x)).ker) :
    N.IsSymplecticOn (N.exteriorDerivative
      (N.pullback (lgManifold n) j.map (lambda0Form n))) Set.univ := by
  apply (N.isSymplecticOn_exteriorDerivative_iff
    (N.pullback (lgManifold n) j.map (lambda0Form n))
    (N.isSmoothForm_pullback_one (lgManifold n) j.map (lambda0Form n)
      (isSmoothForm_lambda0Form n)) Set.univ).mpr
  exact fun x _ => nondegenerate_pullback_lambda0Form_of_tangent_kernel I N j x (hkernel x)

/-- Every actual full far-fiber embedding carries the exact symplectic
restriction of the original primitive. The regular-level tangent-kernel
theorem supplies the geometric hypothesis of the restriction argument. -/
theorem isSymplecticOn_original_farFiber {n : ℕ} (I : ToricInput n)
    {Aamb R : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    {N : SmoothManifold (2 * n - 2)} (j : N.SmoothEmbedding (lgManifold n))
    (himage : Set.range j.map = FullFiber I R) :
    N.IsSymplecticOn (N.exteriorDerivative
      (N.pullback (lgManifold n) j.map (lambda0Form n))) Set.univ :=
  isSymplecticOn_pullback_lambda0Form_of_tangent_kernel I N j
    (original_farFiber_embedding_tangent_range I hamb hR j himage)

/-- The whole original far fiber has an actual smooth embedded realization
whose literal restricted `lambda0` has symplectic differential. The remaining
full-fiber obligations are its intrinsic complete flow and inclusion marking. -/
theorem exists_original_farFiber_symplecticEmbedding {n : ℕ} (I : ToricInput n)
    {Aamb R : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R) :
    ∃ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
      Set.range j.map = FullFiber I R ∧
      N.IsSymplecticOn (N.exteriorDerivative
        (N.pullback (lgManifold n) j.map (lambda0Form n))) Set.univ := by
  obtain ⟨N, j, himage⟩ := exists_original_farFiber_smoothEmbedding I hamb hR
  exact ⟨N, j, himage, isSymplecticOn_original_farFiber I hamb hR j himage⟩

end Geometry

end FsFltz
