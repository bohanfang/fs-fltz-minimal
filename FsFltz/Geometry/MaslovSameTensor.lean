import FsFltz.Geometry.CompatibleComplexPath

/-!
# Maslov homotopy for representatives with equal squared tensors

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244;
`geometric-part-fsf-proof.tex`, `lem:grading`, lines 1994–2030. A common
canonical tensor is fixed by normalized endpoint transport, so the actual
compatible-structure path gives a homotopy with the prescribed endpoints.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry

/-- A common squared canonical tensor is unchanged by normalized transport
in one tangent slot. Complex linearity for both structures is essential. -/
theorem squaredCanonicalTensor_update_compatibleComplexTransport {n : ℕ}
    (J₀ J₁ : Model (2 * n) →L[ℝ] Model (2 * n))
    (s : SquaredCanonicalTensor n) (h₀ : IsSquaredCanonicalTensor J₀ s)
    (h₁ : IsSquaredCanonicalTensor J₁ s)
    (v : Fin n ⊕ Fin n → Model (2 * n)) (i : Fin n ⊕ Fin n) :
    s (Function.update v i (compatibleComplexTransport J₀ J₁ (v i))) = s v := by
  have hcomp : s (Function.update v i (J₀ (J₁ (v i)))) = -s v := by
    have h := h₀.2.2 (Function.update v i (J₁ (v i))) i
    simp only [Function.update_self, Function.update_idem] at h
    rw [h, h₁.2.2 v i]
    simp only [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  simp only [compatibleComplexTransport, smul_apply, sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply]
  rw [s.map_update_smul, s.map_update_sub, Function.update_eq_self, hcomp]
  simp only [sub_neg_eq_add, ← two_smul ℝ (s v), smul_smul]
  norm_num

/-- Normalized transport of every slot fixes a tensor canonical for both
endpoint structures, including the empty-slot case. -/
theorem transportSquaredTensor_eq_self_of_canonical {n : ℕ}
    (J₀ J₁ : Model (2 * n) →L[ℝ] Model (2 * n))
    (s : SquaredCanonicalTensor n) (h₀ : IsSquaredCanonicalTensor J₀ s)
    (h₁ : IsSquaredCanonicalTensor J₁ s) : transportSquaredTensor J₀ J₁ s = s := by
  classical
  ext v
  let A := compatibleComplexTransport J₀ J₁
  have hinvariant (K : Finset (Fin n ⊕ Fin n)) :
      s (fun i => if i ∈ K then A (v i) else v i) = s v := by
    induction K using Finset.induction_on with
    | empty => simp
    | @insert i K hi ih =>
      let w : Fin n ⊕ Fin n → Model (2 * n) := fun j => if j ∈ K then A (v j) else v j
      have hupdate : (fun j => if j ∈ insert i K then A (v j) else v j) =
          Function.update w i (A (w i)) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [w, hi]
        · simp [w, hji]
      rw [hupdate, squaredCanonicalTensor_update_compatibleComplexTransport J₀ J₁ s h₀ h₁ w i]
      exact ih
  simpa only [Finset.mem_univ, ↓reduceIte, transportSquaredTensor,
    ContinuousMultilinearMap.compContinuousLinearMap_apply] using hinvariant Finset.univ

namespace MaslovRepresentative

/-- Equal squared tensor sections on the same two-form determine an actual
smooth homotopy, allowing the compatible structures to differ. -/
theorem homotopic_of_tensor_eq {n : ℕ} {M : SmoothManifold (2 * n)} {eta : M.Form 2}
    (s t : MaslovRepresentative M eta) (h : s.tensor = t.tensor) : MaslovHomotopic s t := by
  obtain ⟨J, hsource, htarget, hcompatible, hsmooth⟩ :=
    exists_smooth_compatibleComplexPath M eta s.J t.J s.compatible t.compatible
  let H := s.homotopyChangeCompatibleStructure J hcompatible hsmooth hsource
  refine ⟨{ family := H.family
            sourceJ := H.sourceJ
            targetJ := htarget
            sourceSection := H.sourceSection
            targetSection := ?_ }⟩
  change (fun x => transportSquaredTensor (s.J x) (J 1 x) (s.tensor x)) = t.tensor
  rw [htarget]
  funext x
  have hcanonical : IsSquaredCanonicalTensor (t.J x) (s.tensor x) := by
    rw [h]
    exact t.canonical x
  exact (transportSquaredTensor_eq_self_of_canonical (s.J x) (t.J x) (s.tensor x)
    (s.canonical x) hcanonical).trans (congrFun h x)

/-- The constructed homotopy makes the two prescribed representatives equal
in the actual quotient of smooth Maslov homotopies. -/
theorem class_eq_of_tensor_eq {n : ℕ} {M : SmoothManifold (2 * n)} {eta : M.Form 2}
    (s t : MaslovRepresentative M eta) (h : s.tensor = t.tensor) :
    (Quot.mk _ s : MaslovClass M eta) = Quot.mk _ t :=
  Quot.sound (s.homotopic_of_tensor_eq t h)

end MaslovRepresentative

end FsFltz.Geometry
