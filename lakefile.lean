import Lake
open Lake DSL

package «dqm-lean» where
  version := v!"1.0.0"

/-- Contour 1A: Pure Constructive Mathematics (`0 external dependencies`, `0 sorryAx`, `0 Classical.choice`). -/
@[default_target]
lean_lib «RotatorCalculusPaper» where
  srcDir := "Constructive"
  roots := #[
    `AxiomGuard,
    `RotatorQuadrature,
    `InverseTrigHyperbolic,
    `LogicCohomology,
    `PillaiDiophantine,
    `AbcPlanetaryWronskian,
    `ModelTheoreticLimit,
    `CollatzPlanetarySplice,
    `RiemannHolonomy,
    `RotatorCalculusPaper
  ]

/-- Contour 1B: Pure Constructive Discrete Quantum Mechanics (`O_2(3) x Z_512`, `0 sorryAx`, `0 Classical.choice`). -/
@[default_target]
lean_lib «MtCarrier» where
  roots := #[`MtCarrier]

@[default_target]
lean_exe «mt_carrier_dump» where
  root := `MtCarrier.DumpJson
