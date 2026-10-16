import FsFltz.Geometry.TailoringCriticalTorusIdentification
import FsFltz.Geometry.TailoringCriticalNormalTrapping
import FsFltz.Geometry.TailoringConormalCoreInclusion

/-!
# Compact forward orbits lie in the actual conormal section

Source: `geometric-part-fsf-proof.tex`, `thm:core`, lines 1728–1750.
The same classified torus is identified with the produced normal datum,
so the constructed trapping neighborhood applies to the actual late orbit.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace FsFltz
open Geometry Set Filter Function
open scoped Topology ContDiff Manifold
variable {n : ℕ}

/-- The two directions of the intrinsic full-core characterization use
actual critical data and actual both-time conormal invariance. -/
theorem tailoringEndpoint_exists_uniform_compactOrbit_iff_coreSection
    (I : ToricInput n) {φEnd φ : RealSpace n → ℝ}
    (hStrong : IsStronglyCompatibleEndPotential I φEnd)
    (hEnd1 : ContDiff ℝ 1 φEnd) (hEnd0 : φEnd 0 = 0)
    {d : ℝ} (hd : 0 < d)
    (hconv : ConvexOn ℝ univ (fun u : EuclideanSpace ℝ (Fin n) =>
      φEnd ((EuclideanSpace.equiv (Fin n) ℝ) u) - d * ‖u‖ ^ 2))
    (hEndLowerE : ∀ u : EuclideanSpace ℝ (Fin n),
      d * ‖u‖ ^ 2 ≤ φEnd ((EuclideanSpace.equiv (Fin n) ℝ) u))
    (hbound : ∀ u : EuclideanSpace ℝ (Fin n), u ≠ 0 → ∀ v,
      (2 * d) * ‖v‖ ^ 2 ≤ inner ℝ
        ((fderiv ℝ (gradient (φEnd ∘ EuclideanSpace.equiv (Fin n) ℝ)) u) v) v)
    {a : ℝ} (ha : 0 < a) (hEndLower : ∀ u, a * ‖u‖ ^ 2 ≤ φEnd u)
    {c U : ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (Φ : RealSpace n ≃ₜ RealSpace n) (hΦeq : ∀ u, Φ u = coordinateGradient φEnd u)
    (hΦ₀ : Φ 0 = 0) (hΦ : ContDiffOn ℝ ∞ Φ ({0}ᶜ : Set (RealSpace n)))
    (hΦinv : ContDiffOn ℝ ∞ Φ.symm ({0}ᶜ : Set (RealSpace n)))
    {R₀ : ℝ} (hR₀ : 0 < R₀)
    (heq : ∀ u, R₀ ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ β ≥ B₀,
      ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
      range j.map = {y | tailoringFamily I β 1 y = 1} →
      ∀ F : CompleteLiouvilleFlow N
        (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ))),
      ∀ p : N.Point, IsCompact (closure (F.flow.forwardOrbit p)) ↔
        j.map p ∈ tailoringCoreSection I φEnd β := by
  classical
  let Faces := {s : Finset (Lattice n) //
    IsPolytopeFace I.vertices s ∧ s.Nonempty ∧ s ≠ I.vertices}
  let embed : Faces → {s // s ∈ I.vertices.powerset} := fun s =>
    ⟨s.val, Finset.mem_powerset.mpr s.property.1.1⟩
  have hinj : Injective embed := by
    intro s t h
    exact Subtype.ext (congrArg (fun t : {s // s ∈ I.vertices.powerset} => t.val) h)
  let : Finite Faces := Finite.of_injective embed hinj
  have hdatas : ∀ᶠ β : ℝ in atTop, ∀ s : Faces,
      ∃ u q lam B R, Nonempty (CriticalFaceNormalData I φEnd φ β s.val u q lam B R) := by
    apply Filter.eventually_all.mpr
    intro s
    obtain ⟨x, z, _, _, _, _, hD⟩ := hStrong.exists_actual_criticalFaceNormalData
      hEnd1 hEnd0 hd hconv hEndLowerE hbound heq s.property.1 s.property.2.1 s.property.2.2
    exact hD.mono fun β hβ => ⟨_, _, _, _, _, hβ⟩
  obtain ⟨BD, hBD⟩ := eventually_atTop.mp hdatas
  obtain ⟨radii, BO, hBO, hO⟩ := hStrong.exists_fullFiber_identified_omegaLimit_face_torus
    hEnd1 hd hconv ha hEndLower hφ hc hU hlower hupper heq
  obtain ⟨BI, _, hI⟩ := tailoringEndpoint_exists_uniform_fullFiber_conormal_invariance
    I hφ hc hU hlower hupper hStrong Φ hΦeq hΦ₀ hΦ hΦinv hR₀ heq
  obtain ⟨BT, _, hT⟩ := tailoringEndpoint_exists_uniform_criticalFaceNormalTrapping
    I hφ hc hU hlower hupper hStrong hEnd1 hR₀ heq
  refine ⟨max BO (max BD (max BI BT)), hBO.trans_le (le_max_left _ _), ?_⟩
  intro β hβ N j himage F p
  have hβO := (le_max_left _ _).trans hβ
  have hβD := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβI := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))
  have hβT := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))
  obtain ⟨_, hinv, hcompact⟩ := hI β hβI N j himage F
  refine ⟨?_, fun hp => (hcompact p hp).2⟩
  intro hp
  have hclass := (hO β hβO).2.2 N j himage
  obtain ⟨s, _, hnear⟩ := hclass.2.2 F p hp
  obtain ⟨u, q, lam, B, R, ⟨D⟩⟩ := hBD β hβD s
  have hur := hclass.2.1 s u q lam B R D
  obtain ⟨W, V, hV, hKV, hVW, htrap, hflow⟩ := hT β hβT s.val s.property.1
    s.property.2.1 s.property.2.2 u q lam B R D N j himage
    ⟨s.property.2.1.choose, s.property.2.1.choose_spec⟩
  have hnearV : ∀ᶠ t in atTop, F.flow t p ∈ V :=
    hnear V hV (by simpa only [← hur] using hKV)
  obtain ⟨T, hTlate⟩ := eventually_atTop.mp hnearV
  have hstay : flowCore F.flow V (F.flow T p) := by
    intro t ht
    rw [← F.flow.map_add]
    exact hTlate (t + T) (by linarith)
  have hlate : j.map (F.flow T p) ∈ tailoringCoreSection I φEnd β := by
    exact hflow F hstay
  have hback := hinv (-T) hlate
  simpa only [← F.flow.map_add, neg_add_cancel, Flow.map_zero_apply, mem_preimage] using hback

end FsFltz
