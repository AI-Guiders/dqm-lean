import Lake
open Lake DSL

package «dqm-mathlib-bridge» where
  version := v!"1.0.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

/-- Contour 1 (imported locally): Pure Constructive Mathematics & DQM Core. -/
lean_lib «ConstructiveCore» where
  srcDir := "../Constructive"
  roots := #[
    `RotatorQuadrature,
    `LogicCohomology,
    `PillaiDiophantine,
    `AbcPlanetaryWronskian,
    `ModelTheoreticLimit,
    `CollatzPlanetarySplice,
    `RiemannHolonomy
  ]

/-- Contour 2: Standard `mathlib4` interoperability bridge (where classical `Mathlib` definitions live). -/
@[default_target]
lean_lib «MathlibBridge» where
  roots := #[`MathlibBridge]
