import FsFltz.Geometry.PotentialTailoringMarkedAssembly
import FsFltz.Geometry.OriginalParameterGrading

/-!
# The literal original-to-holomorphic presentation junction

Source: `geometric-part-fsf-proof.tex`, assembly, lines 2148–2158;
`geoemtric-part-fsf.tex`, `def:chain`, lines 171–199. The original
initial data supply actual inclusion markings; equality on their full
compact carriers determines the native primitives, including boundary
derivatives. No global agreement off the compact pieces is imposed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold

/-- The full native carrier detects pullbacks, including at its boundary. -/
theorem CompactDomain.pullback_eq_of_eqOn_carrier {d e r : ℕ}
    (D : CompactDomain d) (M : SmoothManifold e)
    (f g : D.extension.SmoothMap M) (he : EqOn f g D.carrier)
    (α : M.Form r) (x : D.extension.Point) (hx : x ∈ D.carrier) :
    D.extension.pullback M f α x = D.extension.pullback M g α x := by
  have hd := D.mfderiv_eq_of_eqOn_carrier M
    (fun _ _ => f.contMDiff.mdifferentiableAt (by simp))
    (fun _ _ => g.contMDiff.mdifferentiableAt (by simp)) he x hx
  unfold SmoothManifold.pullback
  rw [hd, he hx]

/-- An actual inclusion marking determines the compact primitive under
its prescribed smooth embedding, even if its extension differs outside. -/
theorem InclusionMarking.pullback_primitive_on_carrier {d : ℕ}
    {D : LiouvilleDomain d} {C : Completion D} {X : CompleteLiouvilleManifold d}
    {i : D.domain.Point → X.manifold.Point} (q : InclusionMarking C X i)
    (j : D.domain.extension.SmoothEmbedding X.manifold)
    (hi : ∀ x, i x = j.map x.val) (x : D.domain.extension.Point) (hx : x ∈ D.domain.carrier) :
    D.domain.extension.pullback X.manifold j.map X.primitive x = D.liouville.primitive x := by
  let f : D.domain.extension.SmoothMap X.manifold :=
    ⟨q.equiv ∘ C.inclusion.map, q.equiv.contMDiff.comp C.inclusion.map.contMDiff⟩
  have he : EqOn f j.map D.domain.carrier := by
    intro z hz
    exact (q.inclusion ⟨z, hz⟩).trans (hi ⟨z, hz⟩)
  calc
    D.domain.extension.pullback X.manifold j.map X.primitive x =
        D.domain.extension.pullback X.manifold f X.primitive x :=
      (D.domain.pullback_eq_of_eqOn_carrier X.manifold f j.map he X.primitive x hx).symm
    _ = D.domain.extension.pullback C.ambient.manifold C.inclusion.map
        (C.ambient.manifold.pullback X.manifold q.equiv X.primitive) x := by
      exact congrFun (D.domain.extension.pullback_comp C.ambient.manifold X.manifold
        (C.inclusion.map.contMDiff.mdifferentiable (by simp))
        (q.equiv.contMDiff.mdifferentiable (by simp)) X.primitive) x
    _ = D.liouville.primitive x := by
      rw [q.primitive]
      exact C.primitive_on_domain x hx

end FsFltz.Geometry

namespace FsFltz.Geometry.CompletionIdentification
open SmoothManifold

/-- Equal full embedded carriers and literal common-form pullbacks
construct the strict completed pair comparison, including for rank one.
No compact or completed equivalence is assumed. -/
theorem exists_of_commonEmbeddedPair_onCarrier {n : ℕ} (P Q : WitnessedPair n)
    (hE : P.ambientDomain.domain.carrier.Nonempty)
    (hD : P.ribbonDomain.domain.carrier.Nonempty)
    (J : P.ambientDomain.domain.extension.SmoothEmbedding (lgManifold n))
    (K : Q.ambientDomain.domain.extension.SmoothEmbedding (lgManifold n))
    (hambient : J.map '' P.ambientDomain.domain.carrier = K.map '' Q.ambientDomain.domain.carrier)
    (hribbon : (J.comp (P.ambientDomain.domain.boundaryInclusion.comp P.ribbonEmbedding)).map ''
        P.ribbonDomain.domain.carrier =
      (K.comp (Q.ambientDomain.domain.boundaryInclusion.comp Q.ribbonEmbedding)).map ''
        Q.ribbonDomain.domain.carrier)
    (α μ : (lgManifold n).Form 1)
    (hPα : ∀ x ∈ P.ambientDomain.domain.carrier, P.ambientDomain.liouville.primitive x =
      P.ambientDomain.domain.extension.pullback (lgManifold n) J.map α x)
    (hQα : ∀ x ∈ Q.ambientDomain.domain.carrier, Q.ambientDomain.liouville.primitive x =
      Q.ambientDomain.domain.extension.pullback (lgManifold n) K.map α x)
    (hPμ : ∀ x ∈ P.ribbonDomain.domain.carrier, P.ribbonDomain.liouville.primitive x =
      P.ribbonDomain.domain.extension.pullback (lgManifold n)
        (J.comp (P.ambientDomain.domain.boundaryInclusion.comp P.ribbonEmbedding)).map μ x)
    (hQμ : ∀ x ∈ Q.ribbonDomain.domain.carrier, Q.ribbonDomain.liouville.primitive x =
      Q.ribbonDomain.domain.extension.pullback (lgManifold n)
        (K.comp (Q.ambientDomain.domain.boundaryInclusion.comp Q.ribbonEmbedding)).map μ x) :
    ∃ I : CompletionIdentification P Q,
      I.scale = 1 ∧ I.shift = (fun _ => 0) ∧
      (∀ x ∈ P.ribbonDomain.domain.carrier,
        (K.comp (Q.ambientDomain.domain.boundaryInclusion.comp Q.ribbonEmbedding)).map
          (I.ribbonEquiv.map x) =
        (J.comp (P.ambientDomain.domain.boundaryInclusion.comp P.ribbonEmbedding)).map x) ∧
      (∀ x ∈ P.ambientDomain.domain.carrier,
        ∃ y ∈ Q.ambientDomain.domain.carrier, K.map y = J.map x ∧
          I.ambientEquiv (P.ambientCompletion.inclusion.map x) =
            Q.ambientCompletion.inclusion.map y) := by
  let R := J.comp (P.ambientDomain.domain.boundaryInclusion.comp P.ribbonEmbedding)
  let S := K.comp (Q.ambientDomain.domain.boundaryInclusion.comp Q.ribbonEmbedding)
  obtain ⟨a, ha, _⟩ := CompactDomain.exists_compactDiffeomorph_of_commonEmbedding
    P.ambientDomain.domain Q.ambientDomain.domain (lgManifold n) hE J K hambient
  obtain ⟨g, hg, _⟩ := CompactDomain.exists_compactDiffeomorph_of_embeddedCarrier
    P.ribbonDomain.domain Q.ribbonDomain.domain (lgManifold n) hD R S hribbon
  have hpa (x) (hx : x ∈ P.ambientDomain.domain.carrier) :
      P.ambientDomain.domain.extension.pullback Q.ambientDomain.domain.extension a.map
        Q.ambientDomain.liouville.primitive x = P.ambientDomain.liouville.primitive x := by
    have he := a.pullback_of_commonEmbedding (lgManifold n) J K ha α x hx
    unfold SmoothManifold.pullback at he ⊢
    rw [hQα _ (a.maps_source hx), hPα x hx]
    exact he
  have hpg (x) (hx : x ∈ P.ribbonDomain.domain.carrier) :
      P.ribbonDomain.domain.extension.pullback Q.ribbonDomain.domain.extension g.map
        Q.ribbonDomain.liouville.primitive x = (1 : ℝ) • P.ribbonDomain.liouville.primitive x := by
    rw [one_smul]
    have he := g.pullback_of_embeddedCarrier (lgManifold n) R S hg μ x hx
    unfold SmoothManifold.pullback at he ⊢
    rw [hQμ _ (g.maps_source hx), hPμ x hx]
    exact he
  have hsquare (x) (hx : x ∈ P.ribbonDomain.domain.carrier) :
      a.map (P.ambientDomain.domain.boundaryInclusion.map (P.ribbonEmbedding.map x)) =
        Q.ambientDomain.domain.boundaryInclusion.map (Q.ribbonEmbedding.map (g.map x)) := by
    apply K.embedding.injective
    have hp : P.ambientDomain.domain.boundaryInclusion.map (P.ribbonEmbedding.map x) ∈
        P.ambientDomain.domain.carrier :=
      P.ambientDomain.domain.boundaryInclusion_mem_carrier _
    rw [ha _ (a.contains_source hp)]
    exact (hg x hx).symm
  obtain ⟨I, hIg, hIc, hIs, hIa⟩ := exists_of_compactPairSquare
    P Q a g hpa 1 zero_lt_one hpg hsquare
  refine ⟨I, hIc, hIs, ?_, ?_⟩
  · intro x hx
    rw [hIg]
    exact hg x hx
  · intro x hx
    exact ⟨a.map x, a.maps_source hx, ha x (a.contains_source hx), hIa x hx⟩


end FsFltz.Geometry.CompletionIdentification

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ} {I : ToricInput n} {φ : RealSpace n → ℝ}
  {β Cplus Aminus K : ℝ} {m : RoundingChoice}

/-- The endpoint of an actual original coefficient family meets the exact
retained holomorphic source by an explicitly constructed strict comparison. -/
theorem PotentialTailoringMarkedPrefix.exists_original_source_identification
    (P : PotentialTailoringMarkedPrefix I φ β Cplus Aminus K m)
    (S : InitialPairData I (Real.exp β) (K / Real.exp β ^ 2) Aminus
      (Cplus ^ 2 * β ^ 2 / 2) m) :
    ∃ q : CompletionIdentification S.pair P.holomorphic.deformation.source,
      q.scale = 1 ∧ q.shift = (fun _ => 0) ∧
      (∀ x ∈ S.pair.ribbonDomain.domain.carrier,
        ((P.holomorphic.embedding parameterZero).comp
          (P.holomorphic.deformation.source.ambientDomain.domain.boundaryInclusion.comp
            P.holomorphic.deformation.source.ribbonEmbedding)).map (q.ribbonEquiv.map x) =
        (S.domainEmbedding.comp
          (S.pair.ambientDomain.domain.boundaryInclusion.comp S.pair.ribbonEmbedding)).map x) ∧
      ∀ x ∈ S.pair.ambientDomain.domain.carrier,
        ∃ y ∈ P.holomorphic.deformation.source.ambientDomain.domain.carrier,
          (P.holomorphic.embedding parameterZero).map y = S.domainEmbedding.map x ∧
          q.ambientEquiv (S.pair.ambientCompletion.inclusion.map x) =
            P.holomorphic.deformation.source.ambientCompletion.inclusion.map y := by
  let R := S.domainEmbedding.comp
    (S.pair.ambientDomain.domain.boundaryInclusion.comp S.pair.ribbonEmbedding)
  let T := (P.holomorphic.embedding parameterZero).comp
    (P.holomorphic.deformation.source.ambientDomain.domain.boundaryInclusion.comp
      P.holomorphic.deformation.source.ribbonEmbedding)
  have hψzero : potentialPath (fun u => realSquaredNorm u / 2) φ 0 =
      (fun u => realSquaredNorm u / 2) := by
    funext u
    simp [potentialPath]
  have hαzero : (lgManifold n).rankTwoPrimitive
      (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ 0))
      (W I) (K / Real.exp β ^ 2) = lambdaKForm I (K / Real.exp β ^ 2) := by
    rw [hψzero, lambdaPotentialForm_quadratic]
    rfl
  have hE : S.pair.ambientDomain.domain.carrier.Nonempty := by
    obtain ⟨x, hx⟩ := S.ribbon_nonempty
    exact ⟨S.pair.ambientDomain.domain.boundaryInclusion.map (S.pair.ribbonEmbedding.map x),
      S.pair.ambientDomain.domain.boundaryInclusion_mem_carrier _⟩
  have hcommonE : S.domainEmbedding.map '' S.pair.ambientDomain.domain.carrier =
      (P.holomorphic.embedding parameterZero).map ''
        P.holomorphic.deformation.source.ambientDomain.domain.carrier := by
    rw [S.domain_image]
    change RoundedDomain I (Real.exp β) (Cplus ^ 2 * β ^ 2 / 2) m =
      (P.holomorphic.embedding parameterZero).map ''
        (P.holomorphic.deformation.pair parameterZero).ambientDomain.domain.carrier
    rw [P.holomorphic.ambient_image parameterZero]
    simp only [parameterZero, potentialPath_roundedDefiningFunction, potentialPath,
      sub_zero, zero_mul, one_mul, add_zero, I.alongCoefficientPath_zero]
    rfl
  have hcommonR : R.map '' S.pair.ribbonDomain.domain.carrier =
      T.map '' P.holomorphic.deformation.source.ribbonDomain.domain.carrier := by
    calc
      R.map '' S.pair.ribbonDomain.domain.carrier =
          (fun x => S.fiber.embedding.map (S.ribbonInFiber.map x)) ''
            S.pair.ribbonDomain.domain.carrier := by
        apply Set.image_congr
        exact S.ribbon_square
      _ = InitialRibbon I (Real.exp β) Aminus := S.ribbon_image
      _ = T.map '' P.holomorphic.deformation.source.ribbonDomain.domain.carrier := by
        change InitialRibbon I (Real.exp β) Aminus =
          ((P.holomorphic.embedding parameterZero).comp
            ((P.holomorphic.deformation.pair parameterZero).ambientDomain.domain.boundaryInclusion.comp
              (P.holomorphic.deformation.pair parameterZero).ribbonEmbedding)).map ''
                (P.holomorphic.deformation.pair parameterZero).ribbonDomain.domain.carrier
        rw [P.holomorphic.ribbon_image parameterZero]
        simp only [parameterZero, potentialPath, sub_zero, zero_mul, one_mul, add_zero,
          I.alongCoefficientPath_zero]
        rfl
  have hPα (x) (hx : x ∈ S.pair.ambientDomain.domain.carrier) :
      S.pair.ambientDomain.liouville.primitive x =
        S.pair.ambientDomain.domain.extension.pullback (lgManifold n) S.domainEmbedding.map
          (lambdaKForm I (K / Real.exp β ^ 2)) x :=
    (S.ambientMarking.pullback_primitive_on_carrier S.domainEmbedding (fun _ => rfl) x hx).symm
  have hQα (x) (_hx : x ∈ P.holomorphic.deformation.source.ambientDomain.domain.carrier) :
      P.holomorphic.deformation.source.ambientDomain.liouville.primitive x =
        P.holomorphic.deformation.source.ambientDomain.domain.extension.pullback (lgManifold n)
          (P.holomorphic.embedding parameterZero).map (lambdaKForm I (K / Real.exp β ^ 2)) x := by
    simpa only [PairDeformation.source, parameterZero, I.alongCoefficientPath_zero, hαzero] using
      congrFun (P.holomorphic.ambient_primitive parameterZero) x
  have hPμ (x) (hx : x ∈ S.pair.ribbonDomain.domain.carrier) :
      S.pair.ribbonDomain.liouville.primitive x =
        S.pair.ribbonDomain.domain.extension.pullback (lgManifold n) R.map (lambda0Form n) x := by
    have h := S.fiberMarking.pullback_primitive_on_carrier S.ribbonInFiber (fun _ => rfl) x hx
    rw [← S.fiber.primitive] at h
    rw [← S.pair.ribbonDomain.domain.extension.pullback_comp S.fiber.ambient.manifold (lgManifold n)
      (S.ribbonInFiber.map.contMDiff.mdifferentiable (by simp))
      (S.fiber.embedding.map.contMDiff.mdifferentiable (by simp))] at h
    have he := S.pair.ribbonDomain.domain.pullback_eq_of_eqOn_carrier (lgManifold n)
      R.map (S.fiber.embedding.comp S.ribbonInFiber).map S.ribbon_square (lambda0Form n) x hx
    exact h.symm.trans he.symm
  have hQμ (x) (_hx : x ∈ P.holomorphic.deformation.source.ribbonDomain.domain.carrier) :
      P.holomorphic.deformation.source.ribbonDomain.liouville.primitive x =
        P.holomorphic.deformation.source.ribbonDomain.domain.extension.pullback (lgManifold n)
          T.map (lambda0Form n) x := by
    simpa only [PairDeformation.source, T, parameterZero, hψzero, lambdaPotentialForm_quadratic] using
      congrFun (P.holomorphic.ribbon_primitive parameterZero) x
  exact CompletionIdentification.exists_of_commonEmbeddedPair_onCarrier
    S.pair P.holomorphic.deformation.source hE S.ribbon_nonempty S.domainEmbedding
    (P.holomorphic.embedding parameterZero) hcommonE hcommonR
    (lambdaKForm I (K / Real.exp β ^ 2)) (lambda0Form n) hPα hQα hPμ hQμ

end FsFltz
