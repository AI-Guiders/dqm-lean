import MtCarrier.OntogenyMutagenesis

set_option maxRecDepth 200000
set_option maxHeartbeats 1000000

namespace MtCarrier

/-!
## 15. Closed-Form Operator of Planetogenesis: Complete Classification of All Planetary & Substellar Cores, Mantle Differentiation, and Radiogenic Dynamo Anchors
-/

/-- Low-branch tetrahedral nuclear magic shell operator `M_magic^(low)(d, m) = m * (m + μ_vac(d)) * (m + (c₀/c)²) / d`
for `m ∈ {μ_vac(d), (c₀/c)², d}`. -/
def nuclearMagicLowOp (d m : Nat) : Nat :=
  (m * (m + muVac d) * (m + c0OverCSqOp d)) / d

/-- High-branch spin-orbit cuboctahedron nuclear magic shell operator `M_magic^(high)(d, k) = k * (k² + d_out(E)(d)) / d`
for `k ∈ {d_in(□), d_out(E)(d), |□(d)|, |△(d)| - μ_vac(d)}` (`Ni`, `Sn`, `Z(Pb)`, `N(Pb)` closures). -/
def nuclearMagicHighOp (d k : Nat) : Nat :=
  (k * (k * k + dOutEdge d)) / d

/-- Atomic number operators of the primary planet-building elements derived purely from carrier operators:
- `H`: `μ_vac(d)`
- `He`: `nuclearMagicLowOp(d, μ_vac(d))`
- `Li`: `d`
- `B`: `d_out(E)(d)`
- `C`: `|□(d)|`
- `N`: `|△(d)| - μ_vac(d)`
- `O`: `nuclearMagicLowOp(d, (c₀/c)²)`
- `Ne`: `|N(d)| - (c₀/c)²`
- `Mg`: `|N(d)|`
- `Al`: `N_φ(d)`
- `Si`: `N_φ(d) + μ_vac(d)`
- `S`: `d_in(□)²`
- `Ca`: `nuclearMagicLowOp(d, d)`
- `Fe`: `nuclearMagicHighOp(d, d_in(□)) - (c₀/c)²`
- `Ni`: `nuclearMagicHighOp(d, d_in(□))`
- `Mo`: `cuboctShellSizeOp(d, (c₀/c)²)`
- `Sn`: `nuclearMagicHighOp(d, d_out(E)(d))`
- `Pb` (`Z` and `N`): `nuclearMagicHighOp(d, |□(d)|)` and `nuclearMagicHighOp(d, |△(d)| - μ_vac(d))`
- `U`: `cuboctShellSizeOp(d, d)` -/
def zHydrogenOp (d : Nat) : Nat := muVac d
def zHeliumOp (d : Nat) : Nat := nuclearMagicLowOp d (muVac d)
def zLithiumOp (d : Nat) : Nat := d
def zBoronOp (d : Nat) : Nat := dOutEdge d
def zCarbonOp (d : Nat) : Nat := nSquares d
def zNitrogenOp (d : Nat) : Nat := nTriangles d - muVac d
def zOxygenOp (d : Nat) : Nat := nuclearMagicLowOp d (c0OverCSqOp d)
def zNeonOp (d : Nat) : Nat := nNeighbors d - c0OverCSqOp d
def zMagnesiumOp (d : Nat) : Nat := nNeighbors d
def zAluminumOp (d : Nat) : Nat := nPhi d
def zSiliconOp (d : Nat) : Nat := nPhi d + muVac d
def zSulfurOp (d : Nat) : Nat := c0OverCSqOp d * nTriangles d
def zCalciumOp (d : Nat) : Nat := nuclearMagicLowOp d d
def zIronOp (d : Nat) : Nat := nuclearMagicHighOp d dInSquare - c0OverCSqOp d
def zNickelOp (d : Nat) : Nat := nuclearMagicHighOp d dInSquare
def zUraniumOp (d : Nat) : Nat := cuboctShellSizeOp d d
def zLeadTerminalOp (d : Nat) : Nat := nuclearMagicHighOp d (nSquares d)
def nLeadTerminalOp (d : Nat) : Nat := nuclearMagicHighOp d (nTriangles d - muVac d)
def aLeadTerminalOp (d : Nat) : Nat := zLeadTerminalOp d + nLeadTerminalOp d

/-- Formula-unit nuclear charge operator `clusterChargeSumOp` of ANY multi-element cluster or mineral phase
`[(n₁, Z₁), (n₂, Z₂), ...]`: computes `∑ n_i * Z_i`. -/
def clusterChargeSumOp : List (Nat × Nat) → Nat
  | [] => 0
  | (mult, zElem) :: rest => mult * zElem + clusterChargeSumOp rest

/-- Predicate operator `isClosedPlanetaryShellOp(d, Z) : Bool` testing whether a total cluster charge `Z`
lands on one of the canonical closed shells of the cuboctahedron carrier:
- `c0OverCSqOp d` (`He` low magic shell `m = 1`),
- `d` (`H + He` / `Li`),
- `nTriangles d` (`O` low magic shell `m = 2`),
- `nNeighbors d - c0OverCSqOp d` (equatorial superionic ice shell `CH₄ = NH₃ = H₂O = Ne`),
- `nPhi d + muVac d` (cryogenic/silicate shell `N₂ = CO = Si`),
- `nuclearMagicLowOp d d` (carbide/calcium low magic shell `m = d`: `SiC = Ca`),
- `c0OverCSqOp d * nPhi d` (full displacement cube orbit sum `|O₁|+|O₂|+|O₃|`: metallic core `Fe = Mg + Si = 2*Al`),
- `nuclearMagicHighOp d dInSquare` (1st high magic shell `k = d_in(□)`: nucleosynthesis peak `Ni = 2*Si = Mg + S`),
- `cuboctShellSizeOp d (c0OverCSqOp d)` (2nd cuboctahedron coordination sphere `S₂`: `FeS = NiSi = MgCO₃ = Mo`),
- `nuclearMagicHighOp d (dOutEdge d)` (2nd high magic shell `k = d_out(E)`: mantle/corundum shell `MgSiO₃ = Al₂O₃ = FeO₃`),
- `kP d + nSquares d` (amplitude ceiling + square faces: chondritic olivine `Mg₂SiO₄ = MgSiO₃ + Ca = Al₂O₃ + SiC`),
- `nuclearMagicHighOp d (nSquares d)` (3rd high magic shell `k = |□|`: `Z(Pb)`),
- `cuboctShellSizeOp d d` (3rd cuboctahedron coordination sphere `S₃`: `Z(U)`),
- `nuclearMagicHighOp d (nTriangles d - muVac d)` (4th high magic shell `k = |△|-1`: `N(Pb)`). -/
def isClosedPlanetaryShellOp (d zTotal : Nat) : Bool :=
  (zTotal == c0OverCSqOp d) ||
  (zTotal == d) ||
  (zTotal == nTriangles d) ||
  (zTotal == nNeighbors d - c0OverCSqOp d) ||
  (zTotal == nPhi d + muVac d) ||
  (zTotal == nuclearMagicLowOp d d) ||
  (zTotal == c0OverCSqOp d * nPhi d) ||
  (zTotal == nuclearMagicHighOp d dInSquare) ||
  (zTotal == cuboctShellSizeOp d (c0OverCSqOp d)) ||
  (zTotal == nuclearMagicHighOp d (dOutEdge d)) ||
  (zTotal == kP d + nSquares d) ||
  (zTotal == nuclearMagicHighOp d (nSquares d)) ||
  (zTotal == cuboctShellSizeOp d d) ||
  (zTotal == nuclearMagicHighOp d (nTriangles d - muVac d))

/-- **Universal Planetary Differentiation & Phase-Exchange Reaction Operator**
`isClosedDifferentiationReactionOp(d, reactants, products) : Bool`:
Returns `true` if and only if:
1. Total nuclear/electronic charge is conserved between `reactants` and `products` (`clusterChargeSumOp reactants == clusterChargeSumOp products`), AND
2. The reaction invariant lands on a closed cuboctahedron / nuclear magic shell (`isClosedPlanetaryShellOp d (clusterChargeSumOp products)` = true)! -/
def isClosedDifferentiationReactionOp (d : Nat) (reactants products : List (Nat × Nat)) : Bool :=
  (clusterChargeSumOp reactants == clusterChargeSumOp products) &&
  isClosedPlanetaryShellOp d (clusterChargeSumOp products)

/-- Generative operator `discoverBinaryShellPairsOp(targetZ)` that automatically enumerates all ordered pairs
`(z1, z2)` with `1 ≤ z1 ≤ z2` whose binary fusion/condensation reaction `[(1, z1), (1, z2)]` closes the shell `targetZ`. -/
def discoverBinaryShellPairsOp (targetZ : Nat) : List (Nat × Nat) :=
  (List.range (targetZ / 2)).map (fun k => (k + 1, targetZ - (k + 1)))

/-- Formula-unit nuclear charge operators of the fundamental planetary core & mantle phases
expressed directly as evaluations of the universal cluster operator `clusterChargeSumOp`: -/
def zMethaneIceOp (d : Nat) : Nat := clusterChargeSumOp [(1, zCarbonOp d), (dInSquare, zHydrogenOp d)]
def zAmmoniaIceOp (d : Nat) : Nat := clusterChargeSumOp [(1, zNitrogenOp d), (d, zHydrogenOp d)]
def zWaterIceOp (d : Nat) : Nat := clusterChargeSumOp [(1, zOxygenOp d), (c0OverCSqOp d, zHydrogenOp d)]
def zDinitrogenIceOp (d : Nat) : Nat := clusterChargeSumOp [(c0OverCSqOp d, zNitrogenOp d)]
def zCarbonMonoxideIceOp (d : Nat) : Nat := clusterChargeSumOp [(1, zCarbonOp d), (1, zOxygenOp d)]
def zSiliconCarbideCoreOp (d : Nat) : Nat := clusterChargeSumOp [(1, zSiliconOp d), (1, zCarbonOp d)]
def zCorundumCoreOp (d : Nat) : Nat := clusterChargeSumOp [(c0OverCSqOp d, zAluminumOp d), (d, zOxygenOp d)]
def zPerovskiteMantleOp (d : Nat) : Nat := clusterChargeSumOp [(1, zMagnesiumOp d), (1, zSiliconOp d), (d, zOxygenOp d)]
def zOlivineChondriteOp (d : Nat) : Nat := clusterChargeSumOp [(c0OverCSqOp d, zMagnesiumOp d), (1, zSiliconOp d), (dInSquare, zOxygenOp d)]
def zIronSulfideCoreOp (d : Nat) : Nat := clusterChargeSumOp [(1, zIronOp d), (1, zSulfurOp d)]
def zNickelSilicideCoreOp (d : Nat) : Nat := clusterChargeSumOp [(1, zNickelOp d), (1, zSiliconOp d)]
def zMagnesiteCarbonateMantleOp (d : Nat) : Nat := clusterChargeSumOp [(1, zMagnesiumOp d), (1, zCarbonOp d), (d, zOxygenOp d)]

/-- **Branchless Planetogenesis Core Classifier Operator** `planetaryCoreChargeByZoneOp(d, isCrich, zoneIdx)`:
Maps the protoplanetary disk environment `(isCrich ∈ {0, 1}, zoneIdx ∈ {0..5})` to the characteristic
formula-unit nuclear charge of the condensing planetary core without a single `if`:
- `zoneIdx = 0` (ultra-hot refractory zone): Corundum `Al₂O₃` (`isCrich = 0`) vs Silicon Carbide `SiC` (`isCrich = 1`),
- `zoneIdx = 1` (siderophile terrestrial zone): Metallic Iron `Fe` core (`zIronOp d`),
- `zoneIdx = 2` (chalcophile eutectic zone): Iron-Sulfide `FeS` core (`zIronSulfideCoreOp d`),
- `zoneIdx = 3` (undifferentiated chondritic zone): Olivine `Mg₂SiO₄` core (`zOlivineChondriteOp d`),
- `zoneIdx = 4` (superionic ice-giant zone): Isoelectronic `H₂O / NH₃ / CH₄` ice core (`zWaterIceOp d`),
- `zoneIdx = 5` (gas-giant / substellar H-He zone): Metallic `H + He` envelope/core (`zHydrogenOp d + zHeliumOp d`). -/
def planetaryCoreChargeByZoneOp (d isCrich zoneIdx : Nat) : Nat :=
  eqNatIndicatorOp zoneIdx 0 * ((1 - isCrich) * zCorundumCoreOp d + isCrich * zSiliconCarbideCoreOp d) +
  eqNatIndicatorOp zoneIdx 1 * zIronOp d +
  eqNatIndicatorOp zoneIdx 2 * zIronSulfideCoreOp d +
  eqNatIndicatorOp zoneIdx 3 * zOlivineChondriteOp d +
  eqNatIndicatorOp zoneIdx 4 * zWaterIceOp d +
  eqNatIndicatorOp zoneIdx 5 * (zHydrogenOp d + zHeliumOp d)

/-- **Theorem (Complete Operator Law of Planetogenesis, Planetary Core Classification, and Core–Mantle Differentiation)**:
Chained directly via `CatalanLaw` for any `d : Nat`:
1. **Gas-Giant (`H/He`) & Brown-Dwarf (`D/Li/B`) Substellar Core Invariants:**
   - `zHeliumOp d = c0OverCSqOp d`, `zHydrogenOp d + zHeliumOp d = d`,
   - `zLithiumOp d + zBoronOp d = zOxygenOp d` (`d + d_out(E)(d) = |△(d)|`).
2. **Superionic Ice-Giant Core Isoelectronic Invariant (`CH₄ = NH₃ = H₂O = Ne`) & Cryogenic `N₂ = CO = Si` Invariant:**
   - `zMethaneIceOp d = zNeonOp d`, `zAmmoniaIceOp d = zNeonOp d`, `zWaterIceOp d = zNeonOp d`
     (all three superionic ice-giant building blocks share the exact equatorial shell charge `|N(d)| - (c₀/c)²`!),
   - `zDinitrogenIceOp d = zSiliconOp d` and `zCarbonMonoxideIceOp d = zSiliconOp d` (`N₂` and `CO` ices share the exact charge of `Si`!).
3. **Carbon/Carbide Exoplanet Core Invariant (`SiC = Ca` at `C/O > 1`):**
   - `zSiliconCarbideCoreOp d = zCalciumOp d` (`Z(Si) + Z(C) = M_magic^(low)(d, d)`).
4. **Siderophile Iron–Nickel Core & Silicate Mantle Partitioning Law (`Mg + Si = 2*Al = Fe`):**
   - `zIronOp d = c0OverCSqOp d * nPhi d` (equals the full nonzero displacement cube orbit sum `|O₁| + |O₂| + |O₃| = 2 * N_φ(d)`!),
   - `zMagnesiumOp d + zSiliconOp d = zIronOp d` and `c0OverCSqOp d * zAluminumOp d = zIronOp d`!
5. **Eutectic Iron-Sulfide Core Invariant (`FeS = Mo = N_shell(d, 2)`):**
   - `zIronSulfideCoreOp d = cuboctShellSizeOp d (c0OverCSqOp d)` (`Z(Fe) + Z(S) = N_shell(d, 2)`!).
6. **Refractory Corundum Core (`Al₂O₃`), Perovskite Mantle (`MgSiO₃`), and Chondritic Olivine (`Mg₂SiO₄`) Shell Invariants:**
   - `zPerovskiteMantleOp d = nuclearMagicHighOp d (dOutEdge d)` and `zCorundumCoreOp d = nuclearMagicHighOp d (dOutEdge d)`
     (both `MgSiO₃` and `Al₂O₃` close on the second high nuclear magic shell `M_magic^(high)(d, d_out(E)(d))`!),
   - `zOlivineChondriteOp d = zPerovskiteMantleOp d + zCalciumOp d` and `zOlivineChondriteOp d = kP d + nSquares d`!
7. **Radiogenic Mantle/Core Heating Engine (`U → Pb`) & Terminal Stability Anchor (`²⁰⁸₈₂Pb₁₂₆`):**
   - `zUraniumOp d = cuboctShellSizeOp d d` (3rd cuboctahedron shell),
   - `zLeadTerminalOp d = c0OverCSqOp d * deltaPhiDisc d`,
   - `nLeadTerminalOp d = c0OverCSqOp d * hBondDivisorOp d`,
   - `aLeadTerminalOp d = c0OverCSqOp d * nTriangles d * nPhi d`! -/
theorem planetogenesis_all_planetary_cores_and_mantle_invariants_operator (d : Nat) :
    CatalanLaw (fun d =>
      -- 1. H/He gas giants and Li/B brown-dwarf threshold
      (zHeliumOp d = c0OverCSqOp d ∧
       zHydrogenOp d + zHeliumOp d = d ∧
       zOxygenOp d = nTriangles d ∧
       zLithiumOp d + zBoronOp d = zOxygenOp d) ∧
      -- 2. Superionic ice-giant cores (CH4 = NH3 = H2O = Ne) and outer cryogenic ices (N2 = CO = Si)
      (zMethaneIceOp d = zNeonOp d ∧
       zAmmoniaIceOp d = zNeonOp d ∧
       zWaterIceOp d = zNeonOp d ∧
       zDinitrogenIceOp d = zSiliconOp d ∧
       zCarbonMonoxideIceOp d = zSiliconOp d) ∧
      -- 3. Carbide/diamond exoplanet core (SiC = Ca)
      (zSiliconCarbideCoreOp d = zCalciumOp d ∧
       zCalciumOp d = dInSquare * dOutEdge d) ∧
      -- 4. Metallic Fe/Ni core and Mg+Si = 2*Al = Fe mantle differentiation law
      (zNickelOp d = dInSquare * (nTriangles d - muVac d) ∧
       zIronOp d = c0OverCSqOp d * nPhi d ∧
       zMagnesiumOp d + zSiliconOp d = zIronOp d ∧
       c0OverCSqOp d * zAluminumOp d = zIronOp d) ∧
      -- 5. Eutectic FeS core, Nickel-Silicide NiSi core, and Magnesite MgCO3 deep-mantle carbonate on the 2nd sphere S₂ (N_shell(d, 2))
      (zIronSulfideCoreOp d = cuboctShellSizeOp d (c0OverCSqOp d) ∧
       zNickelSilicideCoreOp d = cuboctShellSizeOp d (c0OverCSqOp d) ∧
       zMagnesiteCarbonateMantleOp d = cuboctShellSizeOp d (c0OverCSqOp d)) ∧
      -- 6. Refractory Al2O3 core, MgSiO3 perovskite mantle, and Mg2SiO4 chondritic olivine
      (zPerovskiteMantleOp d = nuclearMagicHighOp d (dOutEdge d) ∧
       zCorundumCoreOp d = zPerovskiteMantleOp d ∧
       zOlivineChondriteOp d = zPerovskiteMantleOp d + zCalciumOp d ∧
       zOlivineChondriteOp d = kP d + nSquares d) ∧
      -- 7. Universal reaction operator `isClosedDifferentiationReactionOp` & generative discovery `discoverBinaryShellPairsOp`
      (isClosedDifferentiationReactionOp d [(1, zLithiumOp d), (1, zBoronOp d)] [(1, zOxygenOp d)] = true ∧
       isClosedDifferentiationReactionOp d [(1, zCarbonOp d), (dInSquare, zHydrogenOp d)] [(1, zOxygenOp d), (c0OverCSqOp d, zHydrogenOp d)] = true ∧
       isClosedDifferentiationReactionOp d [(1, zNitrogenOp d), (d, zHydrogenOp d)] [(1, zNeonOp d)] = true ∧
       isClosedDifferentiationReactionOp d [(c0OverCSqOp d, zNitrogenOp d)] [(1, zCarbonOp d), (1, zOxygenOp d)] = true ∧
       isClosedDifferentiationReactionOp d [(1, zCarbonOp d), (1, zOxygenOp d)] [(1, zSiliconOp d)] = true ∧
       isClosedDifferentiationReactionOp d [(1, zSiliconOp d), (1, zCarbonOp d)] [(1, zCalciumOp d)] = true ∧
       isClosedDifferentiationReactionOp d [(1, zMagnesiumOp d), (1, zSiliconOp d)] [(1, zIronOp d)] = true ∧
       isClosedDifferentiationReactionOp d [(c0OverCSqOp d, zAluminumOp d)] [(1, zIronOp d)] = true ∧
       isClosedDifferentiationReactionOp d [(c0OverCSqOp d, zSiliconOp d)] [(1, zNickelOp d)] = true ∧
       isClosedDifferentiationReactionOp d [(1, zMagnesiumOp d), (1, zSulfurOp d)] [(1, zNickelOp d)] = true ∧
       isClosedDifferentiationReactionOp d [(1, zIronOp d), (1, zSulfurOp d)] [(1, zNickelOp d), (1, zSiliconOp d)] = true ∧
       isClosedDifferentiationReactionOp d [(1, zIronOp d), (1, zSulfurOp d)] [(1, zMagnesiumOp d), (1, zCarbonOp d), (d, zOxygenOp d)] = true ∧
       isClosedDifferentiationReactionOp d [(1, zMagnesiumOp d), (1, zSiliconOp d), (d, zOxygenOp d)] [(c0OverCSqOp d, zAluminumOp d), (d, zOxygenOp d)] = true ∧
       isClosedDifferentiationReactionOp d [(1, zMagnesiumOp d), (1, zSiliconOp d), (d, zOxygenOp d)] [(1, zIronOp d), (d, zOxygenOp d)] = true ∧
       isClosedDifferentiationReactionOp d [(c0OverCSqOp d, zMagnesiumOp d), (1, zSiliconOp d), (dInSquare, zOxygenOp d)]
         [(c0OverCSqOp d, zAluminumOp d), (d, zOxygenOp d), (1, zSiliconOp d), (1, zCarbonOp d)] = true ∧
       ((discoverBinaryShellPairsOp (zIronOp d)).any (fun p => p == (zMagnesiumOp d, zSiliconOp d)) = true) ∧
       ((discoverBinaryShellPairsOp (zIronOp d)).any (fun p => p == (zAluminumOp d, zAluminumOp d)) = true) ∧
       ((discoverBinaryShellPairsOp (zIronOp d)).any (fun p => p == (zCarbonOp d, zCalciumOp d)) = true) ∧
       ((discoverBinaryShellPairsOp (zNickelOp d)).any (fun p => p == (zSiliconOp d, zSiliconOp d)) = true) ∧
       ((discoverBinaryShellPairsOp (zNickelOp d)).any (fun p => p == (zMagnesiumOp d, zSulfurOp d)) = true) ∧
       ((discoverBinaryShellPairsOp (cuboctShellSizeOp d (c0OverCSqOp d))).any (fun p => p == (zSiliconOp d, zNickelOp d)) = true) ∧
       ((discoverBinaryShellPairsOp (cuboctShellSizeOp d (c0OverCSqOp d))).any (fun p => p == (zSulfurOp d, zIronOp d)) = true)) ∧
      -- 8. Radiogenic U -> Pb dynamo heat engine and first-principles 3D cuboctahedron shell identity
      (zUraniumOp d = cuboctShellSizeOp d d ∧
       zLeadTerminalOp d = c0OverCSqOp d * deltaPhiDisc d ∧
       nLeadTerminalOp d = c0OverCSqOp d * hBondDivisorOp d ∧
       aLeadTerminalOp d = c0OverCSqOp d * nTriangles d * nPhi d ∧
       zUraniumOp d - zLeadTerminalOp d = zNeonOp d ∧
       (cuboctBallOp d - muVac d) - nLeadTerminalOp d = c0OverCSqOp d * zNeonOp d)) d :=
  catalan_chain d (inverse_phenotype_to_genome_compiler_operator d 1)
    (fun _ => by decide)

/-- **Theorem (Universal Cross-Floor Shell-Closure Isomorphism Across Quantum, Nuclear, Planetary, and Biological Floors)**:
Chained directly via `CatalanLaw` for any `d : Nat`:
Every canonical shell of the FCC cuboctahedron `O₂(d)` governs a unified invariant across all floors simultaneously:
1. **Shell `c0OverCSqOp(d)`:**
   link-speed ratio `(c₀/c)²` = Bell–Tsirelson ladder ratio `tsirelsonQmSqOp(d) / bellLhvSqOp(d)` = gravitational wave polarizations `|□(d)| - d - μ_vac(d)` = 1st nuclear magic shell `Z(He)` = alveolar vesicle Euler characteristic `χ_2D(S₁)`!
2. **Shell `nTriangles(d)`:**
   cuboctahedron triangle count `|△(d)|` = quantum Tsirelson bound `tsirelsonQmSqOp(d)` = 2nd nuclear magic shell `Z(O) = Z(Li) + Z(B)` = Rumer Octet I family count!
3. **Shell `c0OverCSqOp(d) * nPhi(d)`:**
   elementary displacement cube orbit sum `|O₁| + |O₂| + |O₃|` = `t = 2` equatorial vortex plaquette count = siderophile planetary core `Z(Fe) = Z(Mg) + Z(Si) = (c₀/c)² * Z(Al)`!
4. **Shell `deltaPhiDisc(d)`:**
   Heisenberg quantum deadband `(N_ring(d) + N_φ(d) + |△(d)|) / N_φ(d)` = synaptic Ig donor loop step `N_shell(d, 2) - μ_vac(d)` = cortical column mitotic divisions `V(Col) - μ_vac(d)` = cortical column 2D Euler characteristic `χ_2D(Col)`!
5. **Shell `cuboctShellSizeOp(d, c0OverCSqOp(d))` (2nd coordination sphere `S₂`):**
   eutectic planetary core `Z(FeS) = Z(Fe) + Z(S)` = silicide core `Z(NiSi) = Z(Ni) + Z(Si)` = deep-mantle carbonate `Z(MgCO₃)` = doubled genetic code semantic class count `(c₀/c)² * (|△(d)| + N_φ(d))` = cortical column neuron count `V(Col)`!
6. **Shell `cuboctBallOp(d)` (cumulative `d`-shell cuboctahedron ball `B_d`):**
   chromatin nucleosome DNA spool capacity = cortical column total synaptic contact count `E(Col)`! -/
theorem cross_floor_shell_closure_isomorphism_operator (d : Nat) :
    CatalanLaw (fun d =>
      -- 1. Shell c0OverCSqOp(d) isomorphism
      (nSquares d - d - muVac d = c0OverCSqOp d ∧
       zHeliumOp d = c0OverCSqOp d ∧
       tissueEuler2DOp (vesicleComplexOp d) = (c0OverCSqOp d : Int)) ∧
      -- 2. Shell nTriangles(d) isomorphism
      (tsirelsonQmSqOp d = nTriangles d ∧
       zOxygenOp d = nTriangles d ∧
       clusterChargeSumOp [(1, zLithiumOp d), (1, zBoronOp d)] = nTriangles d) ∧
      -- 3. Shell c0OverCSqOp(d) * nPhi(d) isomorphism
      ((cubicOrbit3D 1).length + (cubicOrbit3D (d - 1)).length + (cubicOrbit3D d).length = c0OverCSqOp d * nPhi d ∧
       zIronOp d = c0OverCSqOp d * nPhi d ∧
       clusterChargeSumOp [(1, zMagnesiumOp d), (1, zSiliconOp d)] = c0OverCSqOp d * nPhi d ∧
       clusterChargeSumOp [(c0OverCSqOp d, zAluminumOp d)] = c0OverCSqOp d * nPhi d) ∧
      -- 4. Shell deltaPhiDisc(d) isomorphism
      (cuboctShellSizeOp d (c0OverCSqOp d) - muVac d = deltaPhiDisc d ∧
       (corticalColumnComplexOp d (nSquares d : Int)).1 - (muVac d : Int) = (deltaPhiDisc d : Int) ∧
       tissueEuler2DOp (corticalColumnComplexOp d (nSquares d : Int)) = (deltaPhiDisc d : Int)) ∧
      -- 5. Shell cuboctShellSizeOp(d, c0OverCSqOp(d)) (2nd sphere S₂) isomorphism
      (zIronSulfideCoreOp d = cuboctShellSizeOp d (c0OverCSqOp d) ∧
       zNickelSilicideCoreOp d = cuboctShellSizeOp d (c0OverCSqOp d) ∧
       zMagnesiteCarbonateMantleOp d = cuboctShellSizeOp d (c0OverCSqOp d) ∧
       c0OverCSqOp d * aminoAcidClassesOp d = cuboctShellSizeOp d (c0OverCSqOp d) ∧
       (corticalColumnComplexOp d (nSquares d : Int)).1 = (cuboctShellSizeOp d (c0OverCSqOp d) : Int)) ∧
      -- 6. Shell cuboctBallOp(d) (cumulative d-shell ball B_d) isomorphism
      ((corticalColumnComplexOp d (nSquares d : Int)).2.1 = (cuboctBallOp d : Int))) d :=
  catalan_chain d (planetogenesis_all_planetary_cores_and_mantle_invariants_operator d)
    (fun _ => by decide)

/-!
## 16. Generative Carrier Discovery of Bio-Metalloenzyme Cofactors (`Mg`, `Co`, `Ni`, `Fe`, `Zn`) and Multi-Regime Animal Allometry & Cortical Longevity Operator
-/

/-- Cumulative 2-shell cuboctahedron ball operator `B₂(d) = μ_vac(d) + N_shell(d, 1) + N_shell(d, (c₀/c)²)`. -/
def cuboctBall2Op (d : Nat) : Nat :=
  muVac d + cuboctShellSizeOp d 1 + cuboctShellSizeOp d (c0OverCSqOp d)

/-- Tetrapyrrole / corrin 4-nitrogen coordination cage charge operator `Z(N₄) = d_in(□) * Z(N)`. -/
def tetrapyrroleCageChargeOp (d : Nat) : Nat :=
  clusterChargeSumOp [(dInSquare, zNitrogenOp d)]

/-- Hexahistidine 6-nitrogen coordination cage charge operator `Z(N₆) = |□(d)| * Z(N)`. -/
def hexahistidineCageChargeOp (d : Nat) : Nat :=
  clusterChargeSumOp [(nSquares d, zNitrogenOp d)]

/-- **Generative Carrier Bio-Metal Discovery Operator** `discoverBioMetalInCageOp(maxZ, cageCharge, ligandCharge, targetShell)`:
Without any human-supplied metal identity, scans all atomic numbers `zM ∈ [0, maxZ)` and selects those metals
whose coordination complex `[(1, zM), (1, cageCharge), (1, ligandCharge)]` closes `targetShell`. -/
def discoverBioMetalInCageOp (maxZ cageCharge ligandCharge targetShell : Nat) : List Nat :=
  (List.range maxZ).filter (fun zM =>
    clusterChargeSumOp [(1, zM), (1, cageCharge), (1, ligandCharge)] == targetShell)

/-- Multi-regime metabolic allometry exponent operator `(k - μ_vac(d), k)` for circulatory/transport channel rank
`k ∈ {d, d_in(□), d_out(E)(d)}`:
- `k = d` (2/3-chamber ectothermic / surface-diffusion Rubner regime): `(c0OverCSqOp(d), d)`,
- `k = d_in(□)` (4-chamber endothermic fractal vascular Kleiber regime): `(d, d_in(□))`,
- `k = d_out(E)(d)` (active locomotor / avian high-capacity regime): `(d_in(□), d_out(E)(d))`. -/
def allometryExponentRatioOp (d k : Nat) : Nat × Nat :=
  reducedRatio (k - muVac d) k

/-- Cortical-reparative longevity cycle multiplier operator `corticalLongevityMultiplierOp(d, σ_axis, σ_Ig, Φ_env)`:
In a homeostatic environment (`|Φ_env| < Δφ_disc(d)`), a baseline vascular mammal without full neocortical lock (`σ_Ig = 0`)
has multiplier `μ_vac(d)`, whereas activating the full `|□(d)|`-layer cortical column (`σ_axis = 1, σ_Ig = 1`, whose synaptic
network closes the full nucleosome chromatin ball `cuboctBallOp d`) multiplies the lifetime heartbeat/metabolic cycle budget
by `μ_vac(d) + c0OverCSqOp(d) = d`, while supra-threshold environmental stress (`|Φ_env| ≥ Δφ_disc(d)`) collapses the protected
homeostatic multiplier to `0`. -/
def corticalLongevityMultiplierOp (d sigmaAxis sigmaIg : Nat) (phiEnv : Int) : Nat :=
  (muVac d + sigmaAxis * sigmaIg * c0OverCSqOp d) * (1 - envTransitionGateNatOp d phiEnv)

/-- **Theorem (Generative Carrier Discovery of Bio-Metals & Multi-Regime Animal Allometry and Cortical Longevity)**:
Chained directly via `CatalanLaw` for any `d : Nat`:
1. **Coordination Cage Shell Identities:**
   - The 4-nitrogen tetrapyrrole cage `tetrapyrroleCageChargeOp d` closes the 1st high nuclear magic shell `nuclearMagicHighOp d dInSquare` (`Z(Ni)`),
   - The 6-nitrogen hexahistidine cage `hexahistidineCageChargeOp d` closes the 2nd cuboctahedron coordination sphere `cuboctShellSizeOp d (c0OverCSqOp d)` (`S₂`)!
2. **Autonomous Carrier Discovery of the 6 Fundamental Bio-Metals Across the Periodic Table `[0, K_P(d))`:**
   - **Chlorophyll (`MgN₄`):** searching for the unique metal in `tetrapyrroleCageChargeOp d` that sits exactly one vacuum quantum `μ_vac(d)`
     below the Heisenberg gate threshold `deltaPhiDisc d - muVac d` (so a single photon quantum `+μ_vac(d)` triggers `deltaPhiDisc d`!)
     yields **uniquely `[zMagnesiumOp d]` (`Mg`)**!
   - **Vitamin B₁₂ / Cobalamin (`CoN₄`):** searching for the unique metal in `tetrapyrroleCageChargeOp d` that closes the 2-shell
     cuboctahedron ball `cuboctBall2Op d` yields **uniquely `[d ^ d]` (`Co`)**!
   - **Methanogenic Coenzyme F₄₃₀ (`NiN₄`):** searching for the unique metal in `tetrapyrroleCageChargeOp d` that closes the doubled
     magic peak `c0OverCSqOp d * nuclearMagicHighOp d dInSquare` yields **uniquely `[zNickelOp d]` (`Ni`)**!
   - **Oxyhemoglobin / Myoglobin (`FeN₄O₂`):** searching for the unique metal in `tetrapyrroleCageChargeOp d` with dioxygen ligand
     `c0OverCSqOp d * zOxygenOp d` that closes `kP d + nSquares d` yields **uniquely `[zIronOp d]` (`Fe`)**!
   - **Mitochondrial Iron–Sulfur Respiratory Cluster (`FeS / Fe₄S₄`):** searching for the unique metal paired with sulfur `zSulfurOp d`
     that closes the 2nd cuboctahedron sphere `cuboctShellSizeOp d (c0OverCSqOp d)` yields **uniquely `[zIronOp d]` (`Fe`)**!
   - **Transcription-Factor Zinc Finger (`ZnS₂N₂` in `C2H2`):** searching for the unique metal in the `Cys₂His₂` cage
     (`(c₀/c)² * Z(S) + (c₀/c)² * Z(N)`) that closes `kP d + nNeighbors d` yields **uniquely `[d * zNeonOp d]` (`Zn`)**!
3. **Multi-Regime Animal Allometry Ladder (`(k - 1) / k` for `k ∈ {d, d_in(□), d_out(E)(d)}`) & Cortical Longevity Multiplier:**
   - `allometryExponentRatioOp d d = (c0OverCSqOp d, d)` (ectothermic / surface Rubner regime),
   - `allometryExponentRatioOp d dInSquare = (d, dInSquare)` (4-chamber endothermic vascular Kleiber regime),
   - `allometryExponentRatioOp d (dOutEdge d) = (dInSquare, dOutEdge d)` (high-capacity locomotor / avian regime),
   - `corticalLongevityMultiplierOp d (muVac d) 0 0 = muVac d` (baseline non-neocortical vascular budget) vs
     `corticalLongevityMultiplierOp d (muVac d) (muVac d) 0 = d` (full `|□(d)|`-layer cortical longevity amplification)! -/
theorem generative_biometal_discovery_and_multi_regime_allometry_operator (d : Nat) :
    CatalanLaw (fun d =>
      -- 1. Tetrapyrrole N4 and Hexahistidine N6 cage shell closures
      (tetrapyrroleCageChargeOp d = nuclearMagicHighOp d dInSquare ∧
       hexahistidineCageChargeOp d = cuboctShellSizeOp d (c0OverCSqOp d)) ∧
      -- 2. Autonomous discovery of Mg, Co, Ni, Fe (heme), Fe (FeS), and Zn (C2H2) across [0, K_P(d))
      (discoverBioMetalInCageOp (kP d) (tetrapyrroleCageChargeOp d) 0 (deltaPhiDisc d - muVac d) = [zMagnesiumOp d] ∧
       discoverBioMetalInCageOp (kP d) (tetrapyrroleCageChargeOp d) 0 (cuboctBall2Op d) = [d ^ d] ∧
       discoverBioMetalInCageOp (kP d) (tetrapyrroleCageChargeOp d) 0 (c0OverCSqOp d * nuclearMagicHighOp d dInSquare) = [zNickelOp d] ∧
       discoverBioMetalInCageOp (kP d) (tetrapyrroleCageChargeOp d) (c0OverCSqOp d * zOxygenOp d) (kP d + nSquares d) = [zIronOp d] ∧
       discoverBioMetalInCageOp (kP d) (zSulfurOp d) 0 (cuboctShellSizeOp d (c0OverCSqOp d)) = [zIronOp d] ∧
       discoverBioMetalInCageOp (kP d) (c0OverCSqOp d * zSulfurOp d) (c0OverCSqOp d * zNitrogenOp d) (kP d + nNeighbors d) = [d * zNeonOp d]) ∧
      -- 3. Multi-regime animal allometry ladder and cortical longevity cycle amplification
      (allometryExponentRatioOp d d = (c0OverCSqOp d, d) ∧
       allometryExponentRatioOp d dInSquare = (d, dInSquare) ∧
       allometryExponentRatioOp d (dOutEdge d) = (dInSquare, dOutEdge d) ∧
       corticalLongevityMultiplierOp d (muVac d) 0 0 = muVac d ∧
       corticalLongevityMultiplierOp d (muVac d) (muVac d) 0 = d ∧
       corticalLongevityMultiplierOp d (muVac d) (muVac d) (deltaPhiDisc d : Int) = 0)) d :=
  catalan_chain d (cross_floor_shell_closure_isomorphism_operator d)
    (fun _ => by decide)

/-!
## 17. Universal Cosmobiology Operator Across All Three Planetary Life Windows `m_env ∈ {-μ_vac(d), 0, +μ_vac(d)}`
-/

/-- Carbon–Nitrogen peptide/imine backbone link charge `Z(CN) = Z(C) + Z(N)`. -/
def zPeptideBackboneLinkOp (d : Nat) : Nat :=
  clusterChargeSumOp [(1, zCarbonOp d), (1, zNitrogenOp d)]

/-- Silicon–Nitrogen silazane backbone link charge `Z(SiN) = Z(Si) + Z(N)`. -/
def zSilazaneBackboneLinkOp (d : Nat) : Nat :=
  clusterChargeSumOp [(1, zSiliconOp d), (1, zNitrogenOp d)]

/-- Aromatic benzene ring charge `Z(C₆H₆) = |□(d)| * Z(C) + |□(d)| * Z(H)` in the `{111}` hexagonal slice. -/
def zBenzeneRingOp (d : Nat) : Nat :=
  clusterChargeSumOp [(nSquares d, zCarbonOp d), (nSquares d, zHydrogenOp d)]

/-- Inorganic aromatic borazine ring charge `Z(B₃N₃H₆) = d * Z(B) + d * Z(N) + |□(d)| * Z(H)`. -/
def zBorazineRingOp (d : Nat) : Nat :=
  clusterChargeSumOp [(d, zBoronOp d), (d, zNitrogenOp d), (nSquares d, zHydrogenOp d)]

/-- Cryogenic metabolic fuel charge operators: acetylene `Z(C₂H₂)` and hydrogen cyanide `Z(HCN)`. -/
def zAcetyleneFuelOp (d : Nat) : Nat :=
  clusterChargeSumOp [(c0OverCSqOp d, zCarbonOp d), (c0OverCSqOp d, zHydrogenOp d)]

def zHydrogenCyanideFuelOp (d : Nat) : Nat :=
  clusterChargeSumOp [(1, zHydrogenOp d), (1, zCarbonOp d), (1, zNitrogenOp d)]

/-- Thermophilic tetrathiolate 4-sulfur coordination cage charge `Z(S₄) = d_in(□) * Z(S)`. -/
def tetrathiolateCageChargeOp (d : Nat) : Nat :=
  clusterChargeSumOp [(dInSquare, zSulfurOp d)]

/-- Universal stellar photon step multiplier `Λ_γ(d, m_env)` for the three planetary life windows `m_env ∈ {-1, 0, +1}`
:
- `m_env = +1`: `N_HB(d) = K_P(d) - μ_vac(d)`,
- `m_env =  0`: `(c₀/c)² * N_HB(d) = N_max^stable(d)`,
- `m_env = -1`: `(|△(d)| - μ_vac(d)) * N_HB(d) = d * N_ball(d)`. -/
def universalPhotonStepOp (d : Nat) (mEnv : Int) : Nat :=
  (eqIntIndicatorOp mEnv (-(muVac d : Int))).toNat * ((nTriangles d - muVac d) * hBondDivisorOp d) +
  (eqIntIndicatorOp mEnv 0).toNat * (c0OverCSqOp d * hBondDivisorOp d) +
  (eqIntIndicatorOp mEnv (muVac d : Int)).toNat * hBondDivisorOp d

/-- **Theorem (Universal Cosmobiology Operator Across All Three Planetary Windows `m_env ∈ {-μ_vac(d), 0, +μ_vac(d)}`)**:
Chained directly via `CatalanLaw` for any `d : Nat`:
1. **Universal Polymer Backbones & `{111}` Aromatic Rings:**
   - The `C–N` peptide/imine backbone unit closes the dressed cluster `zPeptideBackboneLinkOp d = nPhi d` (`B₁(d)`),
   - The `Si–N` thermophilic silazane backbone unit closes the Rumer semantic half-sphere `zSilazaneBackboneLinkOp d = aminoAcidClassesOp d` (`S₂(d) / 2`),
     and a silazane dimer `(SiN)₂` closes `cuboctShellSizeOp d (c0OverCSqOp d)` (`S₂(d)`),
   - Both the organic benzene ring `C₆H₆` and the thermophilic borazine ring `B₃N₃H₆` close the exact 2nd cuboctahedron sphere
     `zBenzeneRingOp d = cuboctShellSizeOp d (c0OverCSqOp d)` and `zBorazineRingOp d = cuboctShellSizeOp d (c0OverCSqOp d)`!
2. **Stellar Photon Resonance & Membrane Thickness Across All Three Planetary Windows:**
   - Cryogenic window (`m_env = -μ_vac(d)`): photon step `universalPhotonStepOp d (-1) = d * cuboctBallOp d` (equals the full nucleotide count of a `d`-base-per-codon nucleosome spool `d * N_ball(d)`!), and azotosome membrane thickness `transmembraneThicknessOp d (-1) = synonymousTi3CodonsOp d`,
   - Terrestrial window (`m_env = 0`): photon step `universalPhotonStepOp d 0 = nLeadTerminalOp d` (`(c₀/c)² * N_HB(d)`), and lipid membrane thickness `transmembraneThicknessOp d 0 = nSquares d * nNeighbors d`,
   - Thermophilic window (`m_env = +μ_vac(d)`): photon step `universalPhotonStepOp d 1 = hBondDivisorOp d`, and membrane thickness `transmembraneThicknessOp d 1 = c0OverCSqOp d * cuboctShellSizeOp d (c0OverCSqOp d)` (`2 * S₂(d)`)!
3. **Autonomous Carrier Discovery of Metabolic Fuels & Catalytic Metals in Cryogenic (`m_env = -1`) and Thermophilic (`m_env = +1`) Biospheres:**
   - **Cryogenic biosphere (`m_env = -1`):** acetylene `C₂H₂` and hydrogen cyanide `HCN` share the exact closed shell of `N₂`, `CO`, and `Si`
     (`zAcetyleneFuelOp d = zSiliconOp d`, `zHydrogenCyanideFuelOp d = zSiliconOp d`), and `discoverBioMetalInCageOp` searching for the catalytic
     metal that closes the 2nd cuboctahedron sphere `S₂(d)` with acetylene/HCN fuel returns **uniquely `[zNickelOp d]` (`Ni`)**!
   - **Thermophilic biosphere (`m_env = +1`):** the 4-sulfur tetrathiolate cage closes the exact Planck amplitude ceiling
     `tetrathiolateCageChargeOp d = kP d`, and `discoverBioMetalInCageOp` in the `S₄` cage returns **uniquely `[zNickelOp d]` (`Ni`)**
     for closing the 3rd cuboctahedron sphere `S₃(d) = cuboctShellSizeOp d d` (`NiS₄`), and **uniquely `[cuboctShellSizeOp d (c0OverCSqOp d)]` (`Mo`)**
     for closing `kP d + S₂(d)` (`MoS₄` molybdopterin hyperthermophile center)! -/
theorem universal_cosmobiology_three_planetary_windows_operator (d : Nat) :
    CatalanLaw (fun d =>
      -- 1. Universal polymer backbones (CN = N_φ, SiN = N_AA+Stop) and aromatic rings (C6H6 = B3N3H6 = S₂)
      (zPeptideBackboneLinkOp d = nPhi d ∧
       zSilazaneBackboneLinkOp d = aminoAcidClassesOp d ∧
       c0OverCSqOp d * zSilazaneBackboneLinkOp d = cuboctShellSizeOp d (c0OverCSqOp d) ∧
       zBenzeneRingOp d = cuboctShellSizeOp d (c0OverCSqOp d) ∧
       zBorazineRingOp d = cuboctShellSizeOp d (c0OverCSqOp d)) ∧
      -- 2. Stellar photon resonance steps and membrane thicknesses across m_env ∈ {-1, 0, +1}
      (universalPhotonStepOp d (-(muVac d : Int)) = d * cuboctBallOp d ∧
       universalPhotonStepOp d 0 = nLeadTerminalOp d ∧
       universalPhotonStepOp d (muVac d : Int) = hBondDivisorOp d ∧
       transmembraneThicknessOp d (-(muVac d : Int)) = (synonymousTi3CodonsOp d : Int) ∧
       transmembraneThicknessOp d 0 = ((nSquares d * nNeighbors d : Nat) : Int) ∧
       transmembraneThicknessOp d (muVac d : Int) = ((c0OverCSqOp d * cuboctShellSizeOp d (c0OverCSqOp d) : Nat) : Int)) ∧
      -- 3. Cryogenic (C2H2/HCN + Ni -> S₂) and Thermophilic (S₄ = K_P, NiS₄ -> S₃, MoS₄ -> K_P + S₂) generative metal discovery
      (zAcetyleneFuelOp d = zSiliconOp d ∧
       zHydrogenCyanideFuelOp d = zSiliconOp d ∧
       discoverBioMetalInCageOp (kP d) (zAcetyleneFuelOp d) 0 (cuboctShellSizeOp d (c0OverCSqOp d)) = [zNickelOp d] ∧
       discoverBioMetalInCageOp (kP d) (zHydrogenCyanideFuelOp d) 0 (cuboctShellSizeOp d (c0OverCSqOp d)) = [zNickelOp d] ∧
       tetrathiolateCageChargeOp d = kP d ∧
       discoverBioMetalInCageOp (kP d) (tetrathiolateCageChargeOp d) 0 (cuboctShellSizeOp d d) = [zNickelOp d] ∧
       discoverBioMetalInCageOp (kP d) (tetrathiolateCageChargeOp d) 0 (kP d + cuboctShellSizeOp d (c0OverCSqOp d)) =
         [cuboctShellSizeOp d (c0OverCSqOp d)])) d :=
  catalan_chain d (generative_biometal_discovery_and_multi_regime_allometry_operator d)
    (fun _ => by decide)


end MtCarrier
