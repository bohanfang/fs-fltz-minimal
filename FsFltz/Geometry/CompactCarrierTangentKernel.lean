import FsFltz.Geometry.RegularFiberManifold
import FsFltz.Geometry.BoundaryPresentationBridge

/-!
# Tangent kernel determined by an equation on a native compact carrier

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 996–1009,
and `subsec:fiberends`, lines 1208–1237. The equation is required only on
the actual compact carrier. Its native inclusion detects all tangent
directions at the boundary, so a full-level image hypothesis is unnecessary.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Function

namespace FsFltz.Geometry
open SmoothManifold

/-- An embedded native compact carrier of the regular level's expected
dimension has exactly its tangent kernel, even at the compact boundary.
The kernel equation is derived from the literal scalar/vector level
equation on the whole carrier, rather than supplied as an assumption. -/
theorem compactCarrier_embedding_tangent_range {d : ℕ}
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (D : CompactDomain (d - Module.finrank ℝ F)) (M : SmoothManifold d)
    (j : D.extension.SmoothEmbedding M) (f : M.Point → F) (w : F)
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, F) ∞ f)
    (hregular : ∀ y, f y = w → Function.Surjective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, F) f y))
    (hlevel : ∀ x ∈ D.carrier, f (j.map x) = w) :
    ∀ x ∈ D.carrier,
      (mfderiv 𝓘(ℝ, Model (d - Module.finrank ℝ F)) 𝓘(ℝ, Model d) j.map x).range =
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, F) f (j.map x)).ker := by
  intro x hx
  let A : Model d →L[ℝ] F := mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, F) f (j.map x)
  let B : Model (d - Module.finrank ℝ F) →L[ℝ] Model d :=
    mfderiv 𝓘(ℝ, Model (d - Module.finrank ℝ F)) 𝓘(ℝ, Model d) j.map x
  have hcomp : A.comp B = 0 := by
    by_cases hz : d - Module.finrank ℝ F = 0
    · have hsub : Subsingleton (Model (d - Module.finrank ℝ F)) := by
        rw [hz]
        infer_instance
      ext v
      change A (B v) = 0
      have hv : v = 0 := @Subsingleton.elim _ hsub v 0
      rw [hv, map_zero, map_zero]
    · let : NeZero (d - Module.finrank ℝ F) := ⟨hz⟩
      let p : D.Point := ⟨x, hx⟩
      have hinj := D.injective_mfderiv_subtype_val p
      have hsurj : Function.Surjective (mfderiv (𝓡∂ (d - Module.finrank ℝ F))
          𝓘(ℝ, Model (d - Module.finrank ℝ F))
          (Subtype.val : D.Point → D.extension.Point) p) :=
        LinearMap.injective_iff_surjective.mp hinj
      have hfj : ContMDiff 𝓘(ℝ, Model (d - Module.finrank ℝ F)) 𝓘(ℝ, F) ∞
          (f ∘ j.map) := hf.comp j.map.contMDiff
      have heq : (f ∘ j.map) ∘ (Subtype.val : D.Point → D.extension.Point) =
          fun _ => w := funext (fun y => hlevel y.val y.property)
      have hchain := mfderiv_comp (f := (Subtype.val : D.Point → D.extension.Point))
        (g := f ∘ j.map) p (hfj.mdifferentiableAt (by simp))
        (D.contMDiff_subtype_val.mdifferentiableAt (by simp))
      rw [heq, mfderiv_const] at hchain
      have hzero : mfderiv 𝓘(ℝ, Model (d - Module.finrank ℝ F)) 𝓘(ℝ, F)
          (f ∘ j.map) x = 0 := by
        apply ContinuousLinearMap.ext
        intro v
        obtain ⟨u, rfl⟩ := hsurj v
        exact (congrArg (fun L => L u) hchain).symm
      have h := mfderiv_comp (f := j.map) (g := f) x
        (hf.mdifferentiableAt (by simp)) (j.map.contMDiff.mdifferentiableAt (by simp))
      rw [hzero] at h
      exact h.symm
  have hle : B.range ≤ A.ker := by
    rintro v ⟨u, rfl⟩
    change A (B u) = 0
    exact congrArg (fun L : Model (d - Module.finrank ℝ F) →L[ℝ] F => L u) hcomp
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hdimB : Module.finrank ℝ B.range = d - Module.finrank ℝ F := by
    rw [LinearMap.finrank_range_of_inj (f := B.toLinearMap) (j.immersion x)]
    exact finrank_euclideanSpace_fin
  have hdimA := A.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (hregular (j.map x) (hlevel x hx)), finrank_top] at hdimA
  have hdim : Module.finrank ℝ (Model d) = d := finrank_euclideanSpace_fin
  rw [hdim] at hdimA
  change Module.finrank ℝ B.range = Module.finrank ℝ A.ker
  omega

end FsFltz.Geometry
