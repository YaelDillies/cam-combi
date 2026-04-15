/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import LeanCamCombi.Mathlib.Combinatorics.SimpleGraph.Density
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs

/-!
# Bollobás' graph containment lemma

This file proves Bollobás' lemma on graph containment.
-/

public section

open Asymptotics Filter MeasureTheory ProbabilityTheory
open scoped MeasureTheory ENNReal NNReal SimpleGraph Topology unitInterval

namespace SimpleGraph
variable {V W Ω : Type*} [Fintype W] {G : ℕ → Ω → SimpleGraph V} (H : SimpleGraph W)
  [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ℕ → I}
  (hG : ∀ n, HasLaw (G n) G(V, p n) μ)

/-- **Bollobás' Graph Containment Lemma**, zero statement -/
lemma zero_statement (hH : H.edgeSet.Finite)
    (hp : (fun n ↦ p n : ℕ → ℝ) =o[atTop] (fun n ↦ n ^ (-H.maxEdgeSubdensity⁻¹ : ℝ) : ℕ → ℝ)) :
    Tendsto (fun n ↦ μ {ω | H ⊑ G n ω}) atTop (𝓝 0) :=
  sorry

/-- **Bollobás' Graph Containment Lemma**, one statement -/
lemma one_statement (hH : H.edgeSet.Finite)
    (hp : (fun n ↦ n ^ (-H.maxEdgeSubdensity⁻¹ : ℝ) : ℕ → ℝ) =o[atTop] (fun n ↦ p n : ℕ → ℝ)) :
    Tendsto (fun n ↦ μ {ω | H ⊑ G n ω}) atTop (𝓝 1) :=
  sorry

end SimpleGraph
