import FsFltz

example : FsFltz.GeometricTarget := FsFltz.geometricTarget

#print axioms FsFltz.geometricTarget
#print axioms FsFltz.ToricInput.geometricTargetFor
#print axioms FsFltz.ToricInput.exists_arbitrary_initial_endpointComparison
#print axioms FsFltz.ToricInput.exists_uniform_graded_convenient_comparison
#print axioms FsFltz.PotentialTailoringOriginalMarkedPrefix.exists_graded_chain_with_tailoring_formula
#print axioms FsFltz.PotentialTailoringOriginalMarkedPrefix.graded_chain_of_tailoring_formula
#print axioms FsFltz.PotentialTailoringMarkedPrefix.normalized_junction_gradedLift
#print axioms FsFltz.PotentialTailoringMarkedPrefix.exists_graded_strictJunction_of_completed_native_families
#print axioms FsFltz.PotentialTailoringMarkedPrefix.completed_source_homotopic
#print axioms FsFltz.OuterAmbientInclusionMarkingFamily.maslovFamilyRepresentative_tensor_compact_native
#print axioms FsFltz.CompletedHittingRibbonFamily.maslovFamilyRepresentative_tensor_native
#print axioms FsFltz.CompletedHittingRibbonFamily.exists_graded_cotangentEndpoint_of_hitting_family
#print axioms FsFltz.ToricInput.exists_uniform_original_marked_prefix_fullCore_native_hitting_pairFamilies_with_legendre
#print axioms FsFltz.PotentialTailoringOriginalMarkedPrefix.exists_arbitrary_source_chain
#print axioms FsFltz.Geometry.nonempty_originalInitialPairData
#print axioms FsFltz.Geometry.exists_original_admissible_rounding
#print axioms FsFltz.ToricInput.allNonnegativeComplete

open Lean Elab Command
run_cmd do
  let env ← getEnv
  for (consumer, producer) in [
    (``FsFltz.geometricTarget, ``FsFltz.ToricInput.geometricTargetFor),
    (``FsFltz.ToricInput.geometricTargetFor, ``FsFltz.ToricInput.exists_arbitrary_initial_endpointComparison),
    (``FsFltz.ToricInput.geometricTargetFor, ``FsFltz.ToricInput.allNonnegativeComplete),
    (``FsFltz.ToricInput.geometricTargetFor, ``FsFltz.Geometry.exists_original_admissible_rounding),
    (``FsFltz.ToricInput.geometricTargetFor, ``FsFltz.Geometry.nonempty_originalInitialPairData),
    (``FsFltz.ToricInput.exists_arbitrary_initial_endpointComparison, ``FsFltz.ToricInput.exists_uniform_graded_convenient_comparison),
    (``FsFltz.ToricInput.exists_arbitrary_initial_endpointComparison, ``FsFltz.PotentialTailoringOriginalMarkedPrefix.exists_arbitrary_source_chain),
    (``FsFltz.ToricInput.exists_arbitrary_initial_endpointComparison, ``FsFltz.InitialChoiceComparison.graded),
    (``FsFltz.ToricInput.exists_arbitrary_initial_endpointComparison, ``FsFltz.InitialChoiceComparison.source_prescribed),
    (``FsFltz.ToricInput.exists_arbitrary_initial_endpointComparison, ``FsFltz.CotangentPairData.verticalMaslov_prescribed),
    (``FsFltz.ToricInput.exists_uniform_graded_convenient_comparison, ``FsFltz.ToricInput.exists_uniform_original_marked_prefix_fullCore_native_hitting_pairFamilies_with_legendre),
    (``FsFltz.ToricInput.exists_uniform_graded_convenient_comparison, ``FsFltz.RetainedLegendrePotential.exists_endpoint_level_threshold),
    (``FsFltz.ToricInput.exists_uniform_graded_convenient_comparison, ``FsFltz.tailoringFamily_exists_uniform_native_planePairing_positivity),
    (``FsFltz.ToricInput.exists_uniform_graded_convenient_comparison, ``FsFltz.PotentialTailoringOriginalMarkedPrefix.exists_graded_chain_with_tailoring_formula),
    (``FsFltz.ToricInput.exists_uniform_graded_convenient_comparison, ``FsFltz.CompletedHittingRibbonFamily.exists_completedGrading_of_native_with_formula),
    (``FsFltz.ToricInput.exists_uniform_graded_convenient_comparison, ``FsFltz.CompletedHittingRibbonFamily.exists_graded_cotangentEndpoint_of_hitting_family),
    (``FsFltz.ToricInput.exists_uniform_graded_convenient_comparison, ``FsFltz.PotentialTailoringMarkedPrefix.exists_graded_strictJunction_of_completed_native_families),
    (``FsFltz.PotentialTailoringOriginalMarkedPrefix.exists_graded_chain_with_tailoring_formula, ``FsFltz.OuterAmbientInclusionMarkingFamily.exists_completedGrading),
    (``FsFltz.PotentialTailoringOriginalMarkedPrefix.exists_graded_chain_with_tailoring_formula, ``FsFltz.PotentialTailoringOriginalMarkedPrefix.graded_chain_of_tailoring_formula),
    (``FsFltz.PotentialTailoringOriginalMarkedPrefix.graded_chain_of_tailoring_formula, ``FsFltz.PotentialTailoringOriginalMarkedPrefix.exists_graded_holomorphicChain),
    (``FsFltz.PotentialTailoringOriginalMarkedPrefix.graded_chain_of_tailoring_formula, ``FsFltz.PotentialTailoringMarkedPrefix.normalized_junction_gradedLift),
    (``FsFltz.PotentialTailoringMarkedPrefix.normalized_junction_gradedLift, ``FsFltz.tailoringNativeMaslov_zeroTime_homotopic_prescribed),
    (``FsFltz.PotentialTailoringMarkedPrefix.normalized_junction_gradedLift, ``FsFltz.Geometry.LiouvilleDomain.FlowCollar.cylindricalMaslovOfNative_homotopic),
    (``FsFltz.PotentialTailoringMarkedPrefix.normalized_junction_gradedLift, ``FsFltz.Geometry.Completion.maslovHomotopic_of_eq_on_compact),
    (``FsFltz.PotentialTailoringMarkedPrefix.normalized_junction_gradedLift, ``FsFltz.OuterAmbientInclusionMarkingFamily.maslovFamilyRepresentative_tensor_eq_cylindrical_of_marked_mem_carrier),
    (``FsFltz.PotentialTailoringMarkedPrefix.completed_source_homotopic, ``FsFltz.tailoringNativeMaslovFamily_tensor_one_eq_decreasing_zero),
    (``FsFltz.PotentialTailoringMarkedPrefix.completed_source_homotopic, ``FsFltz.Geometry.Completion.maslovHomotopic_of_compact_native_square),
    (``FsFltz.PotentialTailoringMarkedPrefix.completed_source_homotopic, ``FsFltz.OuterAmbientInclusionMarkingFamily.maslovFamilyRepresentative_tensor_compact_native),
    (``FsFltz.PotentialTailoringMarkedPrefix.completed_source_homotopic, ``FsFltz.CompletedHittingRibbonFamily.maslovFamilyRepresentative_tensor_native),
    (``FsFltz.PotentialTailoringMarkedPrefix.exists_graded_strictJunction_of_completed_native_families, ``FsFltz.PotentialTailoringMarkedPrefix.exists_graded_strictJunction_into_retained_hitting),
    (``FsFltz.PotentialTailoringMarkedPrefix.exists_graded_strictJunction_of_completed_native_families, ``FsFltz.PotentialTailoringMarkedPrefix.completed_source_homotopic),
    (``FsFltz.PotentialTailoringMarkedPrefix.exists_graded_strictJunction_of_completed_native_families, ``FsFltz.StrictHittingJunction.gradedChain_of_source_homotopic)
  ] do
    let mut pending : List Name := [consumer]
    let mut seen : Std.HashSet Name := {}
    let mut found := false
    while !pending.isEmpty && !found do
      let current := pending.head!
      pending := pending.tail!
      if !seen.contains current then
        seen := seen.insert current
        let some ci := env.find? current | throwError m!"Missing declaration {current}"
        let some body := ci.value? true | throwError m!"Missing body {current}"
        let used := body.getUsedConstants
        if used.contains producer then
          found := true
        else
          for child in used do
            if consumer.isPrefixOf child && child != current then
              pending := child :: pending
    unless found do
      throwError m!"Missing proof-body dependency {consumer} -> {producer}"
  logInfo "Checked 32 substantive producer/field body paths for the exact target."
