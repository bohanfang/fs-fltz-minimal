import FsFltz.Geometry.IntrinsicCollarDefining
import FsFltz.Geometry.IntrinsicCollarGluingDifferential
import FsFltz.Geometry.IntrinsicGluingPrimitive
import FsFltz.Geometry.FormScalarDerivative

/-!
# One-form descent through actual smooth open charts

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–158, and
`sec:lean`, lines 805–814. These generic local calculations are used by
completion gluing; the actual completion chart inverses are produced separately.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.SmoothManifold

private theorem contDiffAt_oneForm_comp_inverseGerm {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (a : G → F [⋀^Fin 1]→L[ℝ] ℝ) (B : G → E →L[ℝ] F) (z : G)
    (ha : ContDiffAt ℝ ∞ a z) (hB : ContDiffAt ℝ ∞ B z) :
    ContDiffAt ℝ ∞ (fun y => (a y).compContinuousLinearMap (B y)) z := by
  let eF := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := F) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  let eE := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  have h := (eF.symm.contDiff.contDiffAt.comp z ha).clm_comp hB
  have hs := eE.contDiff.contDiffAt.comp z h
  convert hs using 1
  ext y vs
  change a y (fun i => B y (vs i)) = a y (fun _ => B y (vs 0))
  congr 1
  funext i
  rw [Fin.eq_zero i]

/-- The local version of one-form pullback smoothness needed for inverse
germs of the actual open patch maps. -/
private theorem contDiffAt_formInChart_pullback {d e : ℕ}
    (X : SmoothManifold d) (N : SmoothManifold e) (g : X.Point → N.Point)
    (β : N.Form 1) (hβ : N.IsSmoothForm β) (a : X.Point) (y : Model d)
    (hy : y ∈ (chartAt (Model d) a).target)
    (hg : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞ g
      ((chartAt (Model d) a).symm y)) :
    ContDiffAt ℝ ∞ (X.formInChart a (X.pullback N g β)) y := by
  let c := chartAt (Model d) a
  let x := c.symm y
  let b := chartAt (Model e) (g x)
  let f := b ∘ g ∘ c.symm
  have hx : g x ∈ b.source := mem_chart_source _ _
  have hA : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ c.symm y :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d)) (x := a)).contMDiffAt
      (c.open_target.mem_nhds hy)
  have hB : ContMDiffAt 𝓘(ℝ, Model e) 𝓘(ℝ, Model e) ∞ b (g x) :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model e)) (x := g x)).contMDiffAt
      (b.open_source.mem_nhds hx)
  have hf : ContDiffAt ℝ ∞ f y := (hB.comp y (hg.comp y hA)).contDiffAt
  have hcoeff : ContDiffAt ℝ ∞ (N.formInChart (g x) β) (f y) :=
    (hβ (g x)).contDiffAt (b.open_target.mem_nhds (b.map_source hx))
  have hs := contDiffAt_oneForm_comp_inverseGerm (fun z => N.formInChart (g x) β (f z))
    (fderiv ℝ f) y (hcoeff.comp y hf) (hf.fderiv_right (by simp))
  have hnb : ∀ᶠ z in 𝓝 y, g (c.symm z) ∈ b.source :=
    (hg.continuousAt.comp (c.continuousAt_symm hy)).preimage_mem_nhds
      (b.open_source.mem_nhds hx)
  have hgd : ∀ᶠ z in 𝓝 x, MDifferentiableAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) g z := by
    have hn := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp
      (hg.of_le (by simp))
    exact hn.mono (fun z hz => hz.mdifferentiableAt (by simp))
  apply hs.congr_of_eventuallyEq
  filter_upwards [c.open_target.mem_nhds hy, hnb,
    (c.continuousAt_symm hy).eventually hgd] with z hz hzb hzg
  exact X.formInChart_pullback N β a (g x) z hz hzb hzg

theorem contDiffAt_formInChart_of_inverse {d : ℕ}
    (X N : SmoothManifold d) (γ : X.Form 1) (β : N.Form 1)
    (hβ : N.IsSmoothForm β) (i : N.Point → X.Point)
    (hi : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ i)
    (hrestrict : N.pullback X i γ = β) (a : X.Point) (y : Model d)
    (hy : y ∈ (chartAt (Model d) a).target) (g : X.Point → N.Point)
    (hg : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ g
      ((chartAt (Model d) a).symm y))
    (heq : i ∘ g =ᶠ[𝓝 ((chartAt (Model d) a).symm y)] id) :
    ContDiffAt ℝ ∞ (X.formInChart a γ) y := by
  let c := chartAt (Model d) a
  let x := c.symm y
  have hgd : ∀ᶠ z in 𝓝 x, MDifferentiableAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) g z := by
    have hn := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp
      (hg.of_le (by simp))
    exact hn.mono (fun z hz => hz.mdifferentiableAt (by simp))
  have hform : ∀ᶠ z in 𝓝 x, γ z = X.pullback N g β z := by
    filter_upwards [hgd, eventually_mem_nhds_iff.mpr heq] with z hgz hzn
    have hzi : z ∈ {q | i (g q) = q} := mem_of_mem_nhds hzn
    have heqz : i ∘ g =ᶠ[𝓝 z] id := hzn
    have hid := heqz.mfderiv_eq (I := 𝓘(ℝ, Model d)) (I' := 𝓘(ℝ, Model d))
    have hchain := mfderiv_comp z (hi.mdifferentiableAt (by simp)) hgz
    have hd : (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) i (g z)).comp
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) g z) = ContinuousLinearMap.id ℝ _ := by
      rw [← hchain]
      exact hid.trans (by rw [mfderiv_id]; rfl)
    have hr := congrFun hrestrict (g z)
    ext vs
    unfold SmoothManifold.pullback at hr ⊢
    rw [← hr]
    change γ z vs = γ (i (g z)) (fun n =>
      ((mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) i (g z)).comp
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) g z)) (vs n))
    rw [hd, hzi]
    rfl
  have hc : X.formInChart a γ =ᶠ[𝓝 y] X.formInChart a (X.pullback N g β) := by
    filter_upwards [(c.continuousAt_symm hy).eventually hform] with z hz
    exact congrArg (fun A => A.compContinuousLinearMap
      (X.inverseChartTangentMap a z)) hz
  exact (contDiffAt_formInChart_pullback X N g β hβ a y hy hg).congr_of_eventuallyEq hc

/-- The tangent equivalence of an actual smooth map with bijective derivative. -/
def tangentEquivOfBijective {d : ℕ} (N X : SmoothManifold d)
    (i : N.Point → X.Point) (u : N.Point)
    (h : Function.Bijective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) i u)) :
    Model d ≃L[ℝ] Model d :=
  (LinearEquiv.ofBijective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) i u).toLinearMap
    h).toContinuousLinearEquiv

/-- Push a one-form through the inverse of the actual patch derivative. -/
def pushOneForm {d : ℕ} (N X : SmoothManifold d) (i : N.Point → X.Point)
    (hbij : ∀ u, Function.Bijective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) i u))
    (β : N.Form 1) (u : N.Point) : Model d [⋀^Fin 1]→L[ℝ] ℝ :=
  (β u).compContinuousLinearMap
    (tangentEquivOfBijective N X i u (hbij u)).symm.toContinuousLinearMap

theorem pullback_pushOneForm {d : ℕ} (N X : SmoothManifold d)
    (i : N.Point → X.Point)
    (hbij : ∀ u, Function.Bijective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) i u))
    (β : N.Form 1) (u : N.Point) :
    (pushOneForm N X i hbij β u).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) i u) = β u := by
  ext vs
  change β u (fun j => (tangentEquivOfBijective N X i u (hbij u)).symm
    ((tangentEquivOfBijective N X i u (hbij u)) (vs j))) = _
  simp only [ContinuousLinearEquiv.symm_apply_apply]

/-- Surjectivity lets equality of actual pullbacks test every tangent. -/
theorem form_eq_of_comp_eq {d r : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : Model d [⋀^Fin r]→L[ℝ] ℝ) (T : E →L[ℝ] Model d)
    (hT : Function.Surjective T)
    (h : A.compContinuousLinearMap T = B.compContinuousLinearMap T) : A = B := by
  ext vs
  choose ws hws using fun j => hT (vs j)
  have he := congrArg (fun C => C ws) h
  simpa only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def, hws] using he

/-- Compatible pieces descend to one smooth form through their actual open
patch maps. Local smooth inverse germs are used only to prove smoothness. -/
theorem exists_smoothForm_of_two_open_patches {d : ℕ}
    (X N P : SmoothManifold d) (i : N.Point → X.Point) (j : P.Point → X.Point)
    (hi : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ i)
    (hj : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ j)
    (hinj : Function.Injective i) (hjinj : Function.Injective j)
    (hibij : ∀ u, Function.Bijective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) i u))
    (hjbij : ∀ v, Function.Bijective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) j v))
    (hinv : ∀ u, ∃ g : X.Point → N.Point,
      ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ g (i u) ∧
        i ∘ g =ᶠ[𝓝 (i u)] id)
    (hjnv : ∀ v, ∃ g : X.Point → P.Point,
      ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ g (j v) ∧
        j ∘ g =ᶠ[𝓝 (j v)] id)
    (hcover : ∀ x, (∃ u, i u = x) ∨ ∃ v, j v = x)
    (β : N.Form 1) (η : P.Form 1) (hβ : N.IsSmoothForm β) (hη : P.IsSmoothForm η)
    (hcompat : ∀ u v, i u = j v →
      pushOneForm N X i hibij β u = pushOneForm P X j hjbij η v) :
    ∃ γ : X.Form 1, X.IsSmoothForm γ ∧
      N.pullback X i γ = β ∧ P.pullback X j γ = η := by
  classical
  let γ : X.Form 1 := fun x => if h : ∃ u, i u = x then
    pushOneForm N X i hibij β h.choose
    else pushOneForm P X j hjbij η ((hcover x).resolve_left h).choose
  have hγi (u : N.Point) : γ (i u) = pushOneForm N X i hibij β u := by
    have h : ∃ v, i v = i u := ⟨u, rfl⟩
    have he : h.choose = u := hinj h.choose_spec
    simp only [γ, dite_eq_left h, he]
  have hγj (v : P.Point) : γ (j v) = pushOneForm P X j hjbij η v := by
    by_cases h : ∃ u, i u = j v
    · simp only [γ, dite_eq_left h]
      exact hcompat h.choose v h.choose_spec
    · have he : ((hcover (j v)).resolve_left h).choose = v :=
        hjinj ((hcover (j v)).resolve_left h).choose_spec
      simp only [γ, dite_eq_right h, he]
  have hpi : N.pullback X i γ = β := by
    funext u
    change (γ (i u)).compContinuousLinearMap _ = β u
    rw [hγi]
    exact pullback_pushOneForm N X i hibij β u
  have hpj : P.pullback X j γ = η := by
    funext v
    change (γ (j v)).compContinuousLinearMap _ = η v
    rw [hγj]
    exact pullback_pushOneForm P X j hjbij η v
  refine ⟨γ, ?_, hpi, hpj⟩
  intro a y hy
  let x := (chartAt (Model d) a).symm y
  rcases hcover x with ⟨u, hu⟩ | ⟨v, hv⟩
  · obtain ⟨g, hg, heq⟩ := hinv u
    rw [hu] at hg heq
    exact (contDiffAt_formInChart_of_inverse X N γ β hβ i hi hpi
      a y hy g hg heq).contDiffWithinAt
  · obtain ⟨g, hg, heq⟩ := hjnv v
    rw [hv] at hg heq
    exact (contDiffAt_formInChart_of_inverse X P γ η hη j hj hpj
      a y hy g hg heq).contDiffWithinAt

/-- Actual exterior naturality and a bijective tangent map transport
nondegeneracy from a smooth boundaryless source. -/
theorem nondegenerate_exteriorDerivative_of_pullback {d e : ℕ}
    (N : SmoothManifold d) (X : SmoothManifold e)
    (i : N.Point → X.Point)
    (hi : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞ i)
    (γ : X.Form 1) (hγ : X.IsSmoothForm γ) (β : N.Form 1)
    (hpull : N.pullback X i γ = β) (u : N.Point)
    (hbij : Function.Bijective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) i u))
    (hnd : N.Nondegenerate (N.exteriorDerivative β) u) :
    X.Nondegenerate (X.exteriorDerivative γ) (i u) := by
  have hd := N.exteriorDerivative_pullback X ⟨i, hi⟩ γ hγ
  change N.exteriorDerivative (N.pullback X i γ) =
    N.pullback X i (X.exteriorDerivative γ) at hd
  rw [hpull] at hd
  intro v hv
  obtain ⟨w, hw⟩ := hbij.2 v
  have hw0 : w = 0 := by
    apply hnd
    intro z
    have h := congrArg (fun eta => eta ![w, z]) (congrFun hd u)
    have ht : (fun n : Fin 2 => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) i u
        (![w, z] n)) = ![mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) i u w,
          mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) i u z] := by
      funext n
      fin_cases n <;> rfl
    change N.exteriorDerivative β u ![w, z] =
      X.exteriorDerivative γ (i u) (fun n =>
        mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) i u (![w, z] n)) at h
    rw [ht, hw] at h
    exact h.trans (hv _)
  simpa only [hw0, map_zero] using hw.symm

/-- A bijective differential also transfers target nondegeneracy to the
actual exterior derivative of the pulled-back primitive. -/
theorem nondegenerate_exteriorDerivative_pullback {d e : ℕ}
    (N : SmoothManifold d) (X : SmoothManifold e)
    (i : N.Point → X.Point)
    (hi : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞ i)
    (γ : X.Form 1) (hγ : X.IsSmoothForm γ) (u : N.Point)
    (hbij : Function.Bijective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) i u))
    (hnd : X.Nondegenerate (X.exteriorDerivative γ) (i u)) :
    N.Nondegenerate (N.exteriorDerivative (N.pullback X i γ)) u := by
  have hd := N.exteriorDerivative_pullback X ⟨i, hi⟩ γ hγ
  intro v hv
  apply hbij.1
  rw [map_zero]
  apply hnd
  intro w
  obtain ⟨z, rfl⟩ := hbij.2 w
  have h := congrArg (fun eta => eta ![v, z]) (congrFun hd u)
  have ht : (fun n : Fin 2 => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) i u
      (![v, z] n)) = ![mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) i u v,
        mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) i u z] := by
    funext n
    fin_cases n <;> rfl
  change N.exteriorDerivative (N.pullback X i γ) u ![v, z] =
    X.exteriorDerivative γ (i u) (fun n =>
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) i u (![v, z] n)) at h
  rw [ht] at h
  exact h.symm.trans (hv z)

/-- Nonzero constant scaling preserves nondegeneracy of the actual
exterior derivative, by its proved scalar product rule. -/
theorem nondegenerate_exteriorDerivative_const_smul {d : ℕ}
    (N : SmoothManifold d) (β : N.Form 1) (hβ : N.IsSmoothForm β)
    (c : ℝ) (hc : c ≠ 0) (u : N.Point)
    (hnd : N.Nondegenerate (N.exteriorDerivative β) u) :
    N.Nondegenerate (N.exteriorDerivative (fun x => c • β x)) u := by
  intro v hv
  apply hnd
  intro w
  have he := N.evalTwo_exteriorDerivative_smul (fun _ => c) β contMDiff_const hβ u v w
  simp only [scalarDerivative, mfderiv_const, zero_apply,
    zero_mul, add_zero, sub_zero] at he
  have hh : c * evalTwo (N.exteriorDerivative β) u v w = 0 :=
    he.symm.trans (hv w)
  exact (mul_eq_zero.mp hh).resolve_left hc

end FsFltz.Geometry.SmoothManifold
