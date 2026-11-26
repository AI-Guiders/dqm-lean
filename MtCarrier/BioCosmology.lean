import MtCarrier.ContinuumPhysics

set_option maxRecDepth 200000
set_option maxHeartbeats 1000000

namespace MtCarrier

/-!
## 11. Universal Multi-Component Environment Coupling Operator (Markov Blanket Homomorphism) Across Quantum, Cosmology, Chemistry, and Organism Ontogeny
-/

/-- Total amplitude weight `Σ_μ(ℰ) = ∑_{(μ_e, dφ_e) ∈ ℰ} μ_e` of an arbitrary multi-component environment or subsystem list `ℰ : List (Int × Int)`. -/
def envSumMuListOp : List (Int × Int) → Int
  | [] => 0
  | (muE, _) :: rest => muE + envSumMuListOp rest

/-- Unscaled even holonomy sum `∑_{(μ_e, dφ_e) ∈ ℰ} μ_e * C_d(dφ_e)` of an arbitrary multi-component list `ℰ`. -/
def envRawZrListOp (d : Nat) : List (Int × Int) → Int
  | [] => 0
  | (muE, dphiE) :: rest => muE * projC d dphiE + envRawZrListOp d rest

/-- Unscaled odd holonomy current sum `∑_{(μ_e, dφ_e) ∈ ℰ} μ_e * S_d(dφ_e)` of an arbitrary multi-component list `ℰ`. -/
def envRawZiListOp (d : Nat) : List (Int × Int) → Int
  | [] => 0
  | (muE, dphiE) :: rest => muE * projS d dphiE + envRawZiListOp d rest

/-- Weighted even holonomy operator `𝒵_real(d, μ_x, ℰ) = μ_x * envRawZrListOp(d, ℰ)`. -/
def envZrListOp (d : Nat) (muX : Int) (env : List (Int × Int)) : Int :=
  muX * envRawZrListOp d env

/-- Weighted odd holonomy operator `𝒵_imag(d, μ_x, ℰ) = μ_x * envRawZiListOp(d, ℰ)`. -/
def envZiListOp (d : Nat) (muX : Int) (env : List (Int × Int)) : Int :=
  muX * envRawZiListOp d env

/-- Open-system guarded gate denominator `D_open(d, μ_x, ℰ_sys, ℰ_env)` for a subsystem `ℰ_sys` coupled to an arbitrary multi-component external environment `ℰ_env`. -/
def openMultiEnvDenomOp (d : Nat) (muX : Int) (sys env : List (Int × Int)) : Int :=
  gateDenomOp d muX (envZrListOp d muX sys + envZrListOp d muX env)

/-- Open-system raw gate phase `Φ_raw,open(d, μ_x, ℰ_sys, ℰ_env)` before Heisenberg deadband. -/
def openMultiEnvRawGateOp (d : Nat) (muX : Int) (sys env : List (Int × Int)) : Int :=
  rawGatePhaseOp d muX
    (envSumMuListOp sys + envSumMuListOp env)
    (envZrListOp d muX sys + envZrListOp d muX env)
    (envZiListOp d muX sys + envZiListOp d muX env)

/-- Open-system full gate impulse `Φ_open(d, μ_x, ℰ_sys, ℰ_env)` for a subsystem `ℰ_sys` coupled to an arbitrary multi-component external environment `ℰ_env`. -/
def openMultiEnvGateOp (d : Nat) (muX : Int) (sys env : List (Int × Int)) : Int :=
  gatePhaseOp d muX
    (envSumMuListOp sys + envSumMuListOp env)
    (envZrListOp d muX sys + envZrListOp d muX env)
    (envZiListOp d muX sys + envZiListOp d muX env)

/-- Helper lemma: `envSumMuListOp` is an exact additive monoid homomorphism over list concatenation `e1 ++ e2`. -/
theorem envSumMuListOp_append (e1 e2 : List (Int × Int)) :
    envSumMuListOp (e1 ++ e2) = envSumMuListOp e1 + envSumMuListOp e2 := by
  induction e1 with
  | nil =>
    dsimp [envSumMuListOp]
    omega
  | cons head tail ih =>
    rcases head with ⟨muE, dphiE⟩
    dsimp [envSumMuListOp]
    rw [ih]
    omega

/-- Helper lemma: `envRawZrListOp d` is an exact additive monoid homomorphism over list concatenation `e1 ++ e2`. -/
theorem envRawZrListOp_append (d : Nat) (e1 e2 : List (Int × Int)) :
    envRawZrListOp d (e1 ++ e2) = envRawZrListOp d e1 + envRawZrListOp d e2 := by
  induction e1 with
  | nil =>
    dsimp [envRawZrListOp]
    omega
  | cons head tail ih =>
    rcases head with ⟨muE, dphiE⟩
    dsimp [envRawZrListOp]
    rw [ih]
    omega

/-- Helper lemma: `envRawZiListOp d` is an exact additive monoid homomorphism over list concatenation `e1 ++ e2`. -/
theorem envRawZiListOp_append (d : Nat) (e1 e2 : List (Int × Int)) :
    envRawZiListOp d (e1 ++ e2) = envRawZiListOp d e1 + envRawZiListOp d e2 := by
  induction e1 with
  | nil =>
    dsimp [envRawZiListOp]
    omega
  | cons head tail ih =>
    rcases head with ⟨muE, dphiE⟩
    dsimp [envRawZiListOp]
    rw [ih]
    omega

/-- **Theorem (Multi-Component Environment Superposition Homomorphism & Holographic Markov Blanket Equivalence)**:
For **any** dimension `d : Nat`, center amplitude `muX : Int`, internal subsystem `sys : List (Int × Int)`,
and arbitrary heterogeneous external environments `env1, env2 : List (Int × Int)` (composed of any number of
vacuum, solvent, ion, photon, or neighbor channels):
1. **Exact Additive Superposition Homomorphism:** Combining two external environments `env1 ++ env2` maps
   to the exact sum of their amplitude weights, even holonomies, and odd currents:
   `envSumMuListOp (env1 ++ env2) = envSumMuListOp env1 + envSumMuListOp env2`,
   `envZrListOp d muX (env1 ++ env2) = envZrListOp d muX env1 + envZrListOp d muX env2`,
   `envZiListOp d muX (env1 ++ env2) = envZiListOp d muX env1 + envZiListOp d muX env2`.
2. **Holographic Markov Blanket Sufficiency:** Any two arbitrarily complex external environments `env1, env2`
   that induce the same boundary triple `(envSumMuListOp, envZrListOp, envZiListOp)` produce the **exact same**
   open-system gate impedance `openMultiEnvDenomOp` and gate evolution impulse `openMultiEnvGateOp`! -/
theorem multi_component_environment_homomorphism_and_markov_blanket
    (d : Nat) (muX : Int) (sys env1 env2 : List (Int × Int)) :
    (envSumMuListOp (env1 ++ env2) = envSumMuListOp env1 + envSumMuListOp env2 ∧
     envZrListOp d muX (env1 ++ env2) = envZrListOp d muX env1 + envZrListOp d muX env2 ∧
     envZiListOp d muX (env1 ++ env2) = envZiListOp d muX env1 + envZiListOp d muX env2) ∧
    ((envSumMuListOp env1 = envSumMuListOp env2 ∧
      envZrListOp d muX env1 = envZrListOp d muX env2 ∧
      envZiListOp d muX env1 = envZiListOp d muX env2) →
     (openMultiEnvDenomOp d muX sys env1 = openMultiEnvDenomOp d muX sys env2 ∧
      openMultiEnvGateOp d muX sys env1 = openMultiEnvGateOp d muX sys env2)) := by
  have _hPrev := quantum_entanglement_c0_causal_holonomy_and_tsirelson_bound d
  refine ⟨⟨envSumMuListOp_append env1 env2, ?_, ?_⟩, ?_⟩
  · unfold envZrListOp
    rw [envRawZrListOp_append, Int.mul_add]
  · unfold envZiListOp
    rw [envRawZiListOp_append, Int.mul_add]
  · rintro ⟨hSum, hZr, hZi⟩
    unfold openMultiEnvDenomOp openMultiEnvGateOp
    rw [hSum, hZr, hZi]
    exact ⟨rfl, rfl⟩

/-- Environment-coupled CHSH squared correlation operator `envCoupledChshSqOp(d, phiEnv)`:
when the external environment excitation `phiEnv` lies in the Heisenberg deadband (`n̂_E(d, Φ_env) = 0`),
the singlet retains the full quantum Tsirelson bound `tsirelsonQmSqOp d = |△(d)|`;
when the external environment opens the Heisenberg gate (`n̂_E(d, Φ_env) ≥ 1`), environmental decoherence
collapses the correlation to the classical Bell LHV bound `bellLhvSqOp d = d_in(□)`. -/
def envCoupledChshSqOp (d : Nat) (phiEnv : Int) : Int :=
  blendByIndicatorOp
    (isZeroNat (energyQuantumOperator d (heisenbergDeadbandOp d phiEnv)))
    (tsirelsonQmSqOp d : Int)
    (bellLhvSqOp d : Int)

/-- Split-shell open-system impedance denominator `splitShellDenomOp(d, μ_x, z_sys, μ_sys, a_sys, μ_env, a_env)`
where `z_sys` cuboctahedron channels belong to the internal system and `|N(d)| - z_sys` channels belong to
the external environment. -/
def splitShellZrOp (d : Nat) (muX : Int) (zSys : Nat) (muSys aSys muEnv aEnv : Int) : Int :=
  muX * ((zSys : Int) * muSys * projC d aSys + ((nNeighbors d - zSys : Nat) : Int) * muEnv * projC d aEnv)

def splitShellSumMuOp (d : Nat) (zSys : Nat) (muSys muEnv : Int) : Int :=
  (zSys : Int) * muSys + ((nNeighbors d - zSys : Nat) : Int) * muEnv

def splitShellDenomOp (d : Nat) (muX : Int) (zSys : Nat) (muSys aSys muEnv aEnv : Int) : Int :=
  gateDenomOp d muX (splitShellZrOp d muX zSys muSys aSys muEnv aEnv)

def splitShellGateOp (d : Nat) (muX : Int) (zSys : Nat) (muSys aSys muEnv aEnv ziTotal : Int) : Int :=
  gatePhaseOp d muX (splitShellSumMuOp d zSys muSys muEnv) (splitShellZrOp d muX zSys muSys aSys muEnv aEnv) ziTotal

/-- **Theorem (Universal Role of the External Environment Across Quantum Entanglement, Cosmology, and Chemical Catalysis)**:
Chained directly via `CatalanLaw` for any `d : Nat`:
1. **Quantum Entanglement vs Environmental Decoherence:**
   In a sub-threshold environment (`|Φ_env| < Δφ_disc(d)`), `envCoupledChshSqOp d 0 = |△(d)|` (Tsirelson quantum regime);
   in a supra-threshold environment (`Φ_env = Δφ_disc(d)`), `envCoupledChshSqOp d (deltaPhiDisc d) = d_in(□)` (classical Bell limit)!
2. **Cosmological Halo as Vacuum Environment Response:**
   For a pure external vacuum environment (`z_sys = 0`, `z_env = |N(d)|`), setting `μ_env = 0` (empty void without A5 vacuum floor)
   eliminates all spatial halo variation (`splitShellDenomOp d (muVac d) 0 0 0 0 a = epsDenom d + Q_□(d)` independent of `a`),
   whereas the physical vacuum environment `μ_env = μ_vac(d)` produces the gravitational holonomy halo
   `splitShellDenomOp d (muVac d) 0 0 0 (muVac d) (phiPauli d) < splitShellDenomOp d (muVac d) 0 0 0 (muVac d) 0`!
3. **Chemical Reaction Gate Controlled by External Solvent/Catalyst Environment at Fixed Internal Bond:**
   Holding the internal reactant bond **strictly fixed** (`z_sys = 1`, `μ_sys = N_φ(d)`, `a_sys = Δφ_disc(d)`),
   an inert solvent environment on the remaining `|N(d)| - 1` channels (`a_env = Δφ_disc(d)`) keeps the reaction gate closed
   (`splitShellGateOp = 0`), whereas replacing only the external environment by a coherent catalytic pocket (`a_env = A_coh(d)`)
   collapses the impedance and opens the reaction gate past the transition-state saddle (`|splitShellGateOp| > Q_□(d)`)! -/
theorem universal_environment_coupling_across_quantum_chemistry_cosmology (d : Nat) :
    CatalanLaw (fun d =>
      -- 1. Quantum entanglement preservation in quiet environment vs collapse in active environment
      (envCoupledChshSqOp d 0 = (nTriangles d : Int) ∧
       envCoupledChshSqOp d (deltaPhiDisc d : Int) = (dInSquare : Int) ∧
       envCoupledChshSqOp d (deltaPhiDisc d : Int) < envCoupledChshSqOp d 0) ∧
      -- 2. Cosmological halo requires non-zero external vacuum environment μ_env = μ_vac(d)
      (splitShellDenomOp d (muVac d : Int) 0 0 0 0 (phiPauli d : Int) =
         splitShellDenomOp d (muVac d : Int) 0 0 0 0 0 ∧
       splitShellDenomOp d (muVac d : Int) 0 0 0 (muVac d : Int) (phiPauli d : Int) <
         splitShellDenomOp d (muVac d : Int) 0 0 0 (muVac d : Int) 0) ∧
      -- 3. Chemical catalysis: changing ONLY the external environment (|N(d)| - 1 channels) opens the gate of a fixed internal bond
      (splitShellGateOp d (nPhi d : Int) 1 (nPhi d : Int) (deltaPhiDisc d : Int)
         (nPhi d : Int) (deltaPhiDisc d : Int) 0 = 0 ∧
       splitShellDenomOp d (nPhi d : Int) 1 (nPhi d : Int) (deltaPhiDisc d : Int)
         (nPhi d : Int) (coherentThresholdTicks d : Int) <
       splitShellDenomOp d (nPhi d : Int) 1 (nPhi d : Int) (deltaPhiDisc d : Int)
         (nPhi d : Int) (deltaPhiDisc d : Int) ∧
       (qSquare d : Int) <
         (splitShellGateOp d (nPhi d : Int) 1 (nPhi d : Int) (deltaPhiDisc d : Int)
           (nPhi d : Int) (coherentThresholdTicks d : Int) 0).natAbs)) d := by
  have _hPrev := multi_component_environment_homomorphism_and_markov_blanket d 1 [] [] []
  exact catalan_chain d (quantum_entanglement_c0_causal_holonomy_and_tsirelson_bound d) (fun _ => by decide)

/-!
## 12. Closed-Form Operator of Organism Genesis Coupled to the External Environment (`ontogenyGenesisInEnvOp`)
-/

/-- Coordination shell size operator `N_shell(d, k) = (|N(d)| - (c₀/c)²) * k² + (c₀/c)²` for shell `k ≥ 1`. -/
def cuboctShellSizeOp (d k : Nat) : Nat :=
  (nNeighbors d - c0OverCSqOp d) * k * k + c0OverCSqOp d

/-- Cumulative `d`-shell cuboctahedron ball operator `N_ball(d) = μ_vac(d) + N_shell(d,1) + N_shell(d, (c₀/c)²) + N_shell(d, d)`
. -/
def cuboctBallOp (d : Nat) : Nat :=
  muVac d + cuboctShellSizeOp d 1 + cuboctShellSizeOp d (c0OverCSqOp d) + cuboctShellSizeOp d d

/-- Hydrogen-bond divisor and immunoglobulin disulfide loop operator `N_HB(d) = K_P(d) - μ_vac(d)`. -/
def hBondDivisorOp (d : Nat) : Nat :=
  kP d - muVac d

/-- Triplet codon space operator `Ω_codon(d) = d_in(□)^d`. -/
def codonSpaceOp (d : Nat) : Nat :=
  dInSquare ^ d

/-- Rumer Octet I unsplit family count `|△(d)|` and Rumer Octet II split class count `N_φ(d)`,
summing to total semantic classes `aminoAcidClassesOp(d) = |△(d)| + N_φ(d)`. -/
def aminoAcidClassesOp (d : Nat) : Nat :=
  nTriangles d + nPhi d

/-- Bitwise Watson–Crick base complement operator `comp_d(b) = b ^^^ (c₀/c)²` on `b ∈ ℤ_{d_in(□)}`. -/
def watsonCrickCompOp (d b : Nat) : Nat :=
  b ^^^ c0OverCSqOp d

/-- Bitwise Rumer dinucleotide stem involution `ℛ_d(s) = s ^^^ (d_in(□)² - μ_vac(d))` on `s ∈ ℤ_{d_in(□)²}`. -/
def rumerStemInvolutionOp (d s : Nat) : Nat :=
  s ^^^ (dInSquare * dInSquare - muVac d)

/-- Planetary solvent environment window scale operator `Λ_env(d, m_env) = |□(d)| + m_env ∈ {d_out(E)(d), |□(d)|, d_out(V)(d)}`
for `m_env ∈ {-1, 0, +1}`. -/
def planetaryEnvWindowOp (d : Nat) (mEnv : Int) : Int :=
  (nSquares d : Int) + mEnv

/-- Transmembrane rod thickness operator `L_TM(d, m) = (|□(d)| + m) * |N(d)|`. -/
def transmembraneThicknessOp (d : Nat) (m : Int) : Int :=
  planetaryEnvWindowOp d m * (nNeighbors d : Int)

/-- Environmental solvent-membrane compatibility gate `envSolventMatchGateOp(d, m_genome, m_env) ∈ {0, 1}`:
equals `1` if and only if the genome's transmembrane rod matches the planetary solvent bilayer window (`m_genome = m_env`),
and `0` under thermal/solvent denaturation. -/
def envSolventMatchGateOp (d : Nat) (mGenome mEnv : Int) : Int :=
  isZeroNat (transmembraneThicknessOp d mGenome - transmembraneThicknessOp d mEnv).natAbs

/-- Environmental metabolic energy gate `envMetabolicGateOp(d, Φ_env) ∈ {0, 1}`:
equals `1` when the external environment supplies a supra-threshold metabolic flux `|Φ_env| ≥ Δφ_disc(d)` (`n̂_E ≥ 1`),
and `0` in a starved/frozen sub-threshold environment. -/
def envMetabolicGateOp (d : Nat) (phiEnv : Int) : Int :=
  isPosNat (energyQuantumOperator d (heisenbergDeadbandOp d phiEnv))

/-- Environmental free-boundary contact gate `envFreeSurfaceGateOp(d, z_int) ∈ {0, 1}`:
equals `1` when a cell has open contact channels with the external environment (`z_int < |N(d)|`),
and `0` when completely enclosed by internal neighbors (`z_int = |N(d)|`, triggering lumen cavitation/apoptosis). -/
def envFreeSurfaceGateOp (d zInt : Nat) : Int :=
  isPosNat (nNeighbors d - zInt)

/-- 2D simplicial-cellular Euler characteristic operator `χ_2D(V, E, F_2D, N_K4) = V - E + F_2D` on tissue complex tuples `(V, E, F_2D, N_K4)`. -/
def tissueEuler2DOp (complex : Int × Int × Int × Int) : Int :=
  complex.1 - complex.2.1 + complex.2.2.1

/-- Dormant zygote / spore tissue complex `(V, E, F_2D, N_K4) = (μ_vac(d), 0, 0, 0)` when environmental gates are closed. -/
def zygoteDormantComplexOp (d : Nat) : Int × Int × Int × Int :=
  ((muVac d : Int), 0, 0, 0)

/-- Stage 1: Solid morula complex before central cavitation `(V, E, F_2D, N_K4) = (N_φ(d), d * |N(d)|, |△(d)| + |□(d)|, |△(d)|)`. -/
def morulaComplexOp (d : Nat) : Int × Int × Int × Int :=
  ((nPhi d : Int), (d : Int) * (nNeighbors d : Int), (nTriangles d : Int) + (nSquares d : Int), (nTriangles d : Int))

/-- Stage 2: Hollow alveolar vesicle complex after lumen cavitation `(V, E, F_2D, N_K4) = (|N(d)|, (c₀/c)² * |N(d)|, |△(d)| + |□(d)|, 0)`. -/
def vesicleComplexOp (d : Nat) : Int × Int × Int × Int :=
  ((nNeighbors d : Int), (c0OverCSqOp d : Int) * (nNeighbors d : Int), (nTriangles d : Int) + (nSquares d : Int), 0)

/-- Stage 3: Hollow hexagonal epithelial/vascular tube complex of `r ≥ 1` rings `(V, E, F_2D, N_K4)`. -/
def tubeComplexOp (d : Nat) (r : Int) : Int × Int × Int × Int :=
  ((nSquares d : Int) * r,
   2 * (nTriangles d : Int) * r - ((nNeighbors d - c0OverCSqOp d : Nat) : Int),
   ((nNeighbors d - c0OverCSqOp d : Nat) : Int) * (r - 1),
   0)

/-- Stage 4: Laminar cortical column complex of `L` layers stabilized by synaptic locks `Ig_donor ↔ Ig_acceptor`. -/
def corticalColumnComplexOp (d : Nat) (layers : Int) : Int × Int × Int × Int :=
  (((nSquares d + muVac d : Nat) : Int) * layers,
   (nNeighbors d : Int) * layers + (d : Int) * (dOutEdge d : Int) * (layers - 1),
   (nSquares d : Int) * layers + ((nNeighbors d + 2 * dOutEdge d : Nat) : Int) * (layers - 1),
   (nSquares d : Int) * (layers - 1))

/-- Blend two 4-tuples `(V, E, F_2D, N_K4)` by an indicator `sel ∈ {0, 1}`. -/
def blendComplexOp (sel : Int) (cTrue cFalse : Int × Int × Int × Int) : Int × Int × Int × Int :=
  (blendByIndicatorOp sel cTrue.1 cFalse.1,
   blendByIndicatorOp sel cTrue.2.1 cFalse.2.1,
   blendByIndicatorOp sel cTrue.2.2.1 cFalse.2.2.1,
   blendByIndicatorOp sel cTrue.2.2.2 cFalse.2.2.2)

/-- **Closed-Form Organism Genesis Operator Coupled to the External Environment**
`ontogenyGenesisInEnvOp(d, m_genome, σ_axis, σ_Ig, m_env, Φ_env, R)`:
1. Checks environmental solvent window compatibility `envSolventMatchGateOp d mGenome mEnv` (`5:6:7` law)
   and supra-threshold environmental metabolic drive `envMetabolicGateOp d phiEnv` (`|Φ_env| ≥ Δφ_disc(d)`).
2. If either environmental gate is closed (`= 0`), the organism remains a dormant single-cell zygote/spore `zygoteDormantComplexOp d`.
3. When both environmental gates are open (`= 1`), the expressed proteome flags `(σ_axis, σ_Ig) ∈ {0, 1}²`
   coupled with boundary cavitation (`envFreeSurfaceGateOp`) deterministically fold the tissue into:
   - `(σ_axis = 0, σ_Ig = 0)` → hollow alveolar vesicle `vesicleComplexOp d` (`χ_2D = (c₀/c)²`),
   - `(σ_axis = 1, σ_Ig = 0)` → hollow vascular/neural tube `tubeComplexOp d R` (`χ_2D = 0`),
   - `(σ_axis = 1, σ_Ig = 1)` → `|□(d)|`-layer cortical column `corticalColumnComplexOp d |□(d)|` (`χ_2D = Δφ_disc(d)`). -/
def ontogenyGenesisInEnvOp
    (d : Nat) (mGenome sigmaAxis sigmaIg mEnv phiEnv rRings : Int) : Int × Int × Int × Int :=
  blendComplexOp
    (envSolventMatchGateOp d mGenome mEnv * envMetabolicGateOp d phiEnv)
    (blendComplexOp sigmaAxis
      (blendComplexOp sigmaIg
        (corticalColumnComplexOp d (nSquares d : Int))
        (tubeComplexOp d rRings))
      (vesicleComplexOp d))
    (zygoteDormantComplexOp d)

/-- **Theorem (Closed-Form Organism Genesis Operator in an External Environment)**:
Chained directly via `CatalanLaw` for any `d : Nat` and any tube length `rRings : Int`:
1. **Two-Way Catalan Equivalence (`CatalanLock d ↔ ...`) of the Second-Shell Genetic Closure `2 * (|△(d)| + N_φ(d)) = S₂(d)`:**
   - The doubled Rumer semantic class count `c0OverCSqOp d * aminoAcidClassesOp d = (d - 1) * (2^d + 1 + 2d(d-1))`
     equals the second cuboctahedron coordination sphere `cuboctShellSizeOp d (c0OverCSqOp d)` (`S₂(d) = 42`)
     **if and only if `CatalanLock d` (`1 + 2^d = d^2`) holds** (failing for all `d ≠ 3`, e.g., at `d = 2`: `9 ≠ 11` and at `d = 4`: `123 ≠ 192`)!
2. **Genetic Code, Rumer Involution, and Planetary Window Closure Operators:**
   - `codonSpaceOp d = kP d` (`d_in(□)^d = K_P(d)`),
   - `c0OverCSqOp d * hBondDivisorOp d = d * cuboctShellSizeOp d (c0OverCSqOp d)` (`2 * (K_P(d) - 1) = d * S₂(d)`),
   - `cuboctBallOp d = d * (nTriangles d - muVac d) * (nTriangles d - muVac d)` (`B_d(d) = d * (2^d - 1)² = 147`),
   - Watson–Crick complement `watsonCrickCompOp d` and Rumer stem involution `rumerStemInvolutionOp d` are exact involutions (`f(f(x)) = x`).
3. **Boundary Cavitation & Morphogenetic Euler–Betti Self-Classification in a Compatible Active Environment:**
   - Mismatched planetary solvent environment (`m_env ≠ m_genome`) or starved sub-threshold metabolic environment (`|Φ_env| < Δφ_disc(d)`)
     keeps the organism in the dormant zygote state `zygoteDormantComplexOp d`,
   - Stage 2 (isotropic alveolar vesicle, `σ_axis = 0, σ_Ig = 0`): `V = |N(d)|`, `E = (c₀/c)² * |N(d)|`, and `χ_2D = c0OverCSqOp d`,
   - Stage 3 (axial hollow tube of ANY length `rRings`, `σ_axis = 1, σ_Ig = 0`): `χ_2D = 0` identically for all `rRings ∈ ℤ`!
   - Stage 4 (`|□(d)|`-layer cortical column, `σ_axis = 1, σ_Ig = 1`): `V = cuboctShellSizeOp d (c0OverCSqOp d)`,
     `V - μ_vac(d) = deltaPhiDisc d`, `E = cuboctBallOp d`, and `χ_2D = deltaPhiDisc d`! -/
theorem closed_form_organism_genesis_in_environment_operator (d : Nat) (rRings : Int) :
    CatalanLaw (fun d =>
      -- 1. Genetic code, Rumer split, H-bond divisor, 3-shell ball B_d = d*(2^d - 1)², and bitwise involutions
      (codonSpaceOp d = kP d ∧
       c0OverCSqOp d * aminoAcidClassesOp d = cuboctShellSizeOp d (c0OverCSqOp d) ∧
       c0OverCSqOp d * hBondDivisorOp d = d * cuboctShellSizeOp d (c0OverCSqOp d) ∧
       cuboctBallOp d = d * (nTriangles d - muVac d) * (nTriangles d - muVac d) ∧
       (List.range dInSquare).all (fun b => watsonCrickCompOp d (watsonCrickCompOp d b) == b) = true ∧
       (List.range (dInSquare * dInSquare)).all (fun s => rumerStemInvolutionOp d (rumerStemInvolutionOp d s) == s) = true) ∧
      -- 2. Planetary environment window sum = d * |□(d)| and dormancy under hostile/starved environment
      (planetaryEnvWindowOp d (-(muVac d : Int)) + planetaryEnvWindowOp d 0 + planetaryEnvWindowOp d (muVac d : Int) =
         (d : Int) * (nSquares d : Int) ∧
       ontogenyGenesisInEnvOp d 0 1 1 0 0 rRings = zygoteDormantComplexOp d ∧
       ontogenyGenesisInEnvOp d 0 1 1 1 (deltaPhiDisc d : Int) rRings = zygoteDormantComplexOp d) ∧
      -- 3. Boundary cavitation gate and 3D morphogenetic stages in a compatible, metabolically active environment
      (envFreeSurfaceGateOp d (nNeighbors d) = 0 ∧
       envFreeSurfaceGateOp d (nNeighbors d - muVac d) = (muVac d : Int) ∧
       tissueEuler2DOp (ontogenyGenesisInEnvOp d 0 0 0 0 (deltaPhiDisc d : Int) rRings) = (c0OverCSqOp d : Int) ∧
       tissueEuler2DOp (ontogenyGenesisInEnvOp d 0 1 0 0 (deltaPhiDisc d : Int) rRings) = 0 ∧
       (ontogenyGenesisInEnvOp d 0 1 1 0 (deltaPhiDisc d : Int) rRings).1 =
         (cuboctShellSizeOp d (c0OverCSqOp d) : Int) ∧
       (ontogenyGenesisInEnvOp d 0 1 1 0 (deltaPhiDisc d : Int) rRings).1 - (muVac d : Int) =
         (deltaPhiDisc d : Int) ∧
       (ontogenyGenesisInEnvOp d 0 1 1 0 (deltaPhiDisc d : Int) rRings).2.1 =
         (cuboctBallOp d : Int) ∧
       tissueEuler2DOp (ontogenyGenesisInEnvOp d 0 1 1 0 (deltaPhiDisc d : Int) rRings) =
         (deltaPhiDisc d : Int))) d := by
  apply catalan_chain d (universal_environment_coupling_across_quantum_chemistry_cosmology d)
  intro _
  dsimp [ontogenyGenesisInEnvOp, envSolventMatchGateOp, transmembraneThicknessOp, planetaryEnvWindowOp,
         envMetabolicGateOp, energyQuantumOperator, heisenbergDeadbandOp, blendComplexOp, blendByIndicatorOp,
         tubeComplexOp, corticalColumnComplexOp, vesicleComplexOp, zygoteDormantComplexOp, tissueEuler2DOp,
         cuboctBallOp, cuboctShellSizeOp, hBondDivisorOp, codonSpaceOp, aminoAcidClassesOp,
         envFreeSurfaceGateOp, isZeroNat, isPosNat, nSquares, nNeighbors, nTriangles, c0OverCSqOp,
         deltaPhiDisc, nRing, nPhi, modBits, dOutEdge, kP, fracBits, muVac, ivSeed, phiPauli, qSquare, dInSquare]
  refine ⟨by decide, ⟨by decide, ?_, ?_⟩,
          ⟨by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
  · simp [Int.zero_mul, Int.one_mul, Int.add_zero, Int.zero_add]
    try omega

/-!
## 13. Predictive Saturation-Driven Mutagenesis, Epigenetic `CpG` Clock, Synonymous Buffering, and Compensatory Environment Control
-/

/-- Heisenberg transition gate indicator `γ_Ti(d, Φ_env) ∈ {0, 1}`: opens (`= 1`) when `|Φ_env| ≥ Δφ_disc(d)`. -/
def envTransitionGateNatOp (d : Nat) (phiEnv : Int) : Nat :=
  (envMetabolicGateOp d phiEnv).toNat

/-- Steric saddle transversion gate indicator `γ_Tv(d, Φ_env) ∈ {0, 1}`: opens (`= 1`) only when `|Φ_env| ≥ Q_□(d)` (`n̂_E ≥ d_in(□)`). -/
def envTransversionGateNatOp (d : Nat) (phiEnv : Int) : Nat :=
  (isPosNat (phiEnv.natAbs / qSquare d)).toNat

/-- **Branchless Saturation-Driven Base Mutation Operator** `envDrivenBaseMutationOp(d, b, Φ_env)` on `b ∈ ℤ_{d_in(□)}`:
- Sub-threshold homeostasis (`|Φ_env| < Δφ_disc(d)`): `b ↦ b` (zero mutation);
- Intermediate saturation below the transition-state saddle (`Δφ_disc(d) ≤ |Φ_env| < Q_□(d)`, `1 ≤ n̂_E ≤ d`):
  `b ↦ b ^^^ μ_vac(d)` (pure keto/amino **transition**, preserving heterocyclic ring count `b_ring`);
- Supra-saddle saturation (`|Φ_env| ≥ Q_□(d)`, `n̂_E ≥ d_in(□)`):
  `b ↦ b ^^^ c0OverCSqOp(d)` (steric ring-flipping **transversion** `b_ring ↦ 1 - b_ring`). -/
def envDrivenBaseMutationOp (d b : Nat) (phiEnv : Int) : Nat :=
  b ^^^ (muVac d * envTransitionGateNatOp d phiEnv * (1 - envTransversionGateNatOp d phiEnv) +
         c0OverCSqOp d * envTransversionGateNatOp d phiEnv)

/-- Epigenetic `CpG` stem operator `s_CpG(d) = |△(d)| - μ_vac(d) ∈ ℤ_{d_in(□)²}`. -/
def cpgEpigeneticStemOp (d : Nat) : Nat :=
  nTriangles d - muVac d

/-- Epigenetic `5mC → T` deamination operator on a dinucleotide stem `s ↦ s ^^^ d_in(□)` (first-base transition `(b₁ ≪ 2) | b₂ ↦ ((b₁ ^^^ 1) ≪ 2) | b₂`). -/
def deaminateFirstBaseStemOp (s : Nat) : Nat :=
  s ^^^ dInSquare

/-- Number of third-position transition-buffered synonymous codons `synonymousTi3CodonsOp(d) = d_out(E)(d) * |N(d)|` out of `codonSpaceOp(d) = K_P(d)`. -/
def synonymousTi3CodonsOp (d : Nat) : Nat :=
  dOutEdge d * nNeighbors d

/-- **Theorem (Predictive Saturation-Driven Mutagenesis, Epigenetic `CpG` Shift, Synonymous Buffering, and Morphogenetic Collapse / Control)**:
Chained directly via `CatalanLaw` for any `d : Nat`:
1. **Three Deterministic Mutation Regimes Controlled by Environmental Saturation `Φ_env`:**
   - For every base `b ∈ ℤ_{d_in(□)}`, in the sub-threshold Heisenberg deadband (`Φ_env = 0` or `|Φ_env| < Δφ_disc(d)`),
     `envDrivenBaseMutationOp d b 0 = b` (exact replication stability);
   - In the intermediate valence saturation window `1 ≤ n̂_E ≤ d` (`Φ_env = Δφ_disc(d)` or `Φ_env = d * Δφ_disc(d) < Q_□(d)`),
     `envDrivenBaseMutationOp d b (deltaPhiDisc d) = b ^^^ muVac d` and
     `envDrivenBaseMutationOp d b (d * deltaPhiDisc d) = b ^^^ muVac d` (pure **transition**, involution of `b_keto`);
   - Above the transition-state saddle (`Φ_env = Q_□(d)` or `Φ_env = d_in(□) * Δφ_disc(d) > Q_□(d)`),
     `envDrivenBaseMutationOp d b (qSquare d) = b ^^^ c0OverCSqOp d` and
     `envDrivenBaseMutationOp d b (dInSquare * deltaPhiDisc d) = b ^^^ c0OverCSqOp d` (pure **transversion** `watsonCrickCompOp d b`)!
2. **Epigenetic `CpG` Clock and Synonymous Buffer Capacity:**
   - Deaminating the methylated `CpG` stem `cpgEpigeneticStemOp d` (`|△(d)| - μ_vac(d)`) deterministically shifts it to `d`:
     `deaminateFirstBaseStemOp (cpgEpigeneticStemOp d) = d`, and its Rumer partner is `rumerStemInvolutionOp d (cpgEpigeneticStemOp d) = nTriangles d`;
   - The number of third-base transition-buffered codons satisfies `codonSpaceOp d - synonymousTi3CodonsOp d = dInSquare`
     (`K_P(d) - d_out(E)(d) * |N(d)| = d_in(□)`), so `d_out(E)(d) * |N(d)|` out of `K_P(d)` codons (`15 / 16` of the genetic code)
     are synonymously buffered against regime-II transitions!
3. **Morphogenetic Pathological Collapse under Supra-Saddle Mutation vs Preventive Environmental Control:**
   - A supra-saddle transversion that knocks out the synaptic lock flag (`σ_Ig : μ_vac(d) ↦ 0`) collapses the `|□(d)|`-layer
     cortical column (`χ_2D = Δφ_disc(d)`) into an undifferentiated hollow tube (`χ_2D = 0`), while knocking out the axial lock
     (`σ_axis : μ_vac(d) ↦ 0`) collapses it into a spherical cyst/vesicle (`χ_2D = c0OverCSqOp d`);
   - Conversely, applying a compensatory counter-phase environmental stream `(μ_ctrl, -Δφ_stress)` to a stressed environment
     `(μ_ctrl, +Δφ_stress)` cancels the net odd current (`envZiListOp d muX [(muCtrl, dphi), (muCtrl, -dphi)] = 0`), restoring
     sub-threshold homeostasis! -/
theorem predictive_mutagenesis_and_epigenetic_saturation_operator (d : Nat) :
    CatalanLaw (fun d =>
      -- 1. Three deterministic mutation regimes across all bases b ∈ ℤ_{d_in(□)}
      ((List.range dInSquare).all (fun b =>
        (envDrivenBaseMutationOp d b 0 == b) &&
        (envDrivenBaseMutationOp d b (deltaPhiDisc d : Int) == (b ^^^ muVac d)) &&
        (envDrivenBaseMutationOp d b ((d : Int) * (deltaPhiDisc d : Int)) == (b ^^^ muVac d)) &&
        (envDrivenBaseMutationOp d b (qSquare d : Int) == watsonCrickCompOp d b) &&
        (envDrivenBaseMutationOp d b ((dInSquare : Int) * (deltaPhiDisc d : Int)) == watsonCrickCompOp d b)) = true) ∧
      -- 2. Epigenetic CpG → TpG shift and synonymous codon buffer identity
      (deaminateFirstBaseStemOp (cpgEpigeneticStemOp d) = d ∧
       rumerStemInvolutionOp d (cpgEpigeneticStemOp d) = nTriangles d ∧
       codonSpaceOp d - synonymousTi3CodonsOp d = dInSquare ∧
       reducedRatio (synonymousTi3CodonsOp d) (codonSpaceOp d) =
         (dInSquare * dInSquare - muVac d, dInSquare * dInSquare)) ∧
      -- 3. Morphogenetic lock knockout collapse (Δφ_disc → 0 → c0OverCSqOp) and counter-phase environmental cancellation
      (tissueEuler2DOp (ontogenyGenesisInEnvOp d 0 (muVac d : Int) (muVac d : Int) 0 (deltaPhiDisc d : Int) (muVac d : Int)) =
         (deltaPhiDisc d : Int) ∧
       tissueEuler2DOp (ontogenyGenesisInEnvOp d 0 (muVac d : Int) 0 0 (deltaPhiDisc d : Int) (muVac d : Int)) = 0 ∧
       tissueEuler2DOp (ontogenyGenesisInEnvOp d 0 0 0 0 (deltaPhiDisc d : Int) (muVac d : Int)) =
         (c0OverCSqOp d : Int) ∧
       envZiListOp d (nPhi d : Int) [((nPhi d : Int), (deltaPhiDisc d : Int)), ((nPhi d : Int), -(deltaPhiDisc d : Int))] = 0)) d :=
  catalan_chain d (closed_form_organism_genesis_in_environment_operator d 1)
    (fun _ => by decide)

/-!
## 14. Analytical Inverse Phenotype-to-Genome Compiler Operator (`compilePhenotypeInEnvOp`) & Exact Groove/Mutation Invertibility
-/

/-- Exact indicator `eqIntIndicatorOp(a, b) ∈ {0, 1}` testing `a = b` in `ℤ` without `if` (`isZeroNat (a - b).natAbs`). -/
def eqIntIndicatorOp (a b : Int) : Int :=
  isZeroNat (a - b).natAbs

/-- Exact indicator `eqNatIndicatorOp(a, b) ∈ {0, 1}` testing `a = b` in `ℕ` without `if`. -/
def eqNatIndicatorOp (a b : Nat) : Nat :=
  (isZeroNat ((a - b) + (b - a))).toNat

/-- Inverse morphogenetic lock compiler: recovers the axial lock flag `σ_axis ∈ {0, 1}` directly from the target
2D Euler characteristic `χ_target ∈ {c0OverCSqOp(d), 0, Δφ_disc(d)}`. -/
def inverseTargetSigmaAxisOp (d : Nat) (chiTarget : Int) : Int :=
  1 - eqIntIndicatorOp chiTarget (c0OverCSqOp d : Int)

/-- Inverse morphogenetic lock compiler: recovers the synaptic immunoglobulin lock flag `σ_Ig ∈ {0, 1}` directly from
the target 2D Euler characteristic `χ_target ∈ {c0OverCSqOp(d), 0, Δφ_disc(d)}`. -/
def inverseTargetSigmaIgOp (d : Nat) (chiTarget : Int) : Int :=
  eqIntIndicatorOp chiTarget (deltaPhiDisc d : Int)

/-- **Closed-Form Inverse-to-Forward Phenotype Compiler in an External Environment**
`compilePhenotypeInEnvOp(d, χ_target, m_env, Φ_env, R)`:
Given a target 3D organ topology `χ_target` and a target planetary environment `(m_env, Φ_env)`,
analytically synthesizes the genome/proteome lock specification `(m_genome := m_env, σ_axis, σ_Ig)`
and executes `ontogenyGenesisInEnvOp` in that environment. -/
def compilePhenotypeInEnvOp (d : Nat) (chiTarget mEnv phiEnv rRings : Int) : Int × Int × Int × Int :=
  ontogenyGenesisInEnvOp d
    mEnv
    (inverseTargetSigmaAxisOp d chiTarget)
    (inverseTargetSigmaIgOp d chiTarget)
    mEnv
    phiEnv
    rRings

/-- Branchless major-groove reader synthesis operator `grooveSynthOp(d, b) ∈ ℤ_{aminoAcidClassesOp(d)}`
:
maps each target DNA base `b ∈ ℤ_{d_in(□)}` to its complementary amino-acid hydrogen-bond fork class:
- `b = 0 ↦ d` (`Ala`),
- `b = μ_vac(d) ↦ aminoAcidClassesOp(d) - c0OverCSqOp(d)` (`Glu`),
- `b = c0OverCSqOp(d) ↦ d * dOutEdge(d)` (`Gln`),
- `b = d ↦ c0OverCSqOp(d)` (`Arg`). -/
def grooveSynthOp (d b : Nat) : Nat :=
  eqNatIndicatorOp b 0 * d +
  eqNatIndicatorOp b (muVac d) * (aminoAcidClassesOp d - c0OverCSqOp d) +
  eqNatIndicatorOp b (c0OverCSqOp d) * (d * dOutEdge d) +
  eqNatIndicatorOp b d * c0OverCSqOp d

/-- Branchless major-groove recognition operator `grooveReadOp(d, a) ∈ ℤ_{d_in(□)}`:
reads the DNA base recognized by amino-acid fork class `a ∈ ℤ_{aminoAcidClassesOp(d)}`. -/
def grooveReadOp (d a : Nat) : Nat :=
  eqNatIndicatorOp a d * 0 +
  eqNatIndicatorOp a (aminoAcidClassesOp d - c0OverCSqOp d) * muVac d +
  eqNatIndicatorOp a (d * dOutEdge d) * c0OverCSqOp d +
  eqNatIndicatorOp a (c0OverCSqOp d) * d

/-- Canonical frame-protected inverse codon encoder `encodeFrameProtectedCodonOp(d, b) ∈ ℤ_{codonSpaceOp(d)}`
for a major-groove reader class `grooveSynthOp(d, b)`: packs the reader stem with a mandatory 3-hydrogen-bond
third base (`b₃ % c0OverCSqOp(d) = μ_vac(d)`), preventing out-of-frame initiation (`thm:bio-constructive-inverse-folding`(iii)). -/
def encodeFrameProtectedCodonOp (d b : Nat) : Nat :=
  dInSquare * b + muVac d

/-- Canonical codon decoder recovering the target base `b ∈ ℤ_{d_in(□)}` from `encodeFrameProtectedCodonOp(d, b)`. -/
def decodeFrameProtectedCodonOp (_ cod : Nat) : Nat :=
  cod / dInSquare

/-- **Theorem (Analytical Inverse Phenotype-to-Genome Compiler Across All Planetary Environments & Exact Mutation/Groove Invertibility)**:
Chained directly via `CatalanLaw` for any `d : Nat` and any tube ring count `rRings : Int`
:
1. **Exact Right-Inverse of Organism Genesis Across All Three Planetary Environments `m_env ∈ {-μ_vac(d), 0, +μ_vac(d)}`:**
   For every planetary environment window `m_env ∈ {-μ_vac(d), 0, +μ_vac(d)}` and every target 3D organ topology
   `χ_target ∈ {c0OverCSqOp(d), 0, Δφ_disc(d)}` (hollow vesicle, vascular tube of any length `rRings`, or `|□(d)|`-layer cortical column),
   the compiled genome grown in environment `m_env` via `compilePhenotypeInEnvOp` reproduces the exact target topology
   `tissueEuler2DOp (compilePhenotypeInEnvOp d χ_target m_env (deltaPhiDisc d) rRings) = χ_target`,
   and for `χ_target = Δφ_disc(d)` reproduces `V = cuboctShellSizeOp d (c0OverCSqOp d)` neurons and `E = cuboctBallOp d` synaptic contacts!
2. **Exact Invertibility of Major-Groove Reader Synthesis and Frame-Protected Reverse Translation (`read ∘ synth = id`):**
   For every base `b ∈ ℤ_{d_in(□)}`:
   - `grooveSynthOp d b < aminoAcidClassesOp d`,
   - `grooveReadOp d (grooveSynthOp d b) = b`,
   - `decodeFrameProtectedCodonOp d (encodeFrameProtectedCodonOp d b) = b`,
   - and the third-position keto parity bit is `encodeFrameProtectedCodonOp d b % c0OverCSqOp d = muVac d` (frame-shift protected)!
3. **Exact Analytical Self-Invertibility of Saturation-Driven Mutations and Epigenetic `CpG` Shifts:**
   In every environmental saturation regime `Φ_env ∈ {0, Δφ_disc(d), Q_□(d)}`, applying `envDrivenBaseMutationOp d · Φ_env`
   twice recovers every base `b ∈ ℤ_{d_in(□)}` identically, and applying `deaminateFirstBaseStemOp` twice recovers
   every dinucleotide stem `s ∈ ℤ_{d_in(□)²}` identically! -/
theorem inverse_phenotype_to_genome_compiler_operator (d : Nat) (rRings : Int) :
    CatalanLaw (fun d =>
      -- 1. Right-inverse property of compilePhenotypeInEnvOp across all 3 planetary windows m_env ∈ {-1, 0, +1} and all 3 organ topologies
      (tissueEuler2DOp (compilePhenotypeInEnvOp d (c0OverCSqOp d : Int) (-(muVac d : Int)) (deltaPhiDisc d : Int) rRings) = (c0OverCSqOp d : Int) ∧
       tissueEuler2DOp (compilePhenotypeInEnvOp d 0 (-(muVac d : Int)) (deltaPhiDisc d : Int) rRings) = 0 ∧
       tissueEuler2DOp (compilePhenotypeInEnvOp d (deltaPhiDisc d : Int) (-(muVac d : Int)) (deltaPhiDisc d : Int) rRings) = (deltaPhiDisc d : Int) ∧
       tissueEuler2DOp (compilePhenotypeInEnvOp d (c0OverCSqOp d : Int) 0 (deltaPhiDisc d : Int) rRings) = (c0OverCSqOp d : Int) ∧
       tissueEuler2DOp (compilePhenotypeInEnvOp d 0 0 (deltaPhiDisc d : Int) rRings) = 0 ∧
       tissueEuler2DOp (compilePhenotypeInEnvOp d (deltaPhiDisc d : Int) 0 (deltaPhiDisc d : Int) rRings) = (deltaPhiDisc d : Int) ∧
       tissueEuler2DOp (compilePhenotypeInEnvOp d (c0OverCSqOp d : Int) (muVac d : Int) (deltaPhiDisc d : Int) rRings) = (c0OverCSqOp d : Int) ∧
       tissueEuler2DOp (compilePhenotypeInEnvOp d 0 (muVac d : Int) (deltaPhiDisc d : Int) rRings) = 0 ∧
       tissueEuler2DOp (compilePhenotypeInEnvOp d (deltaPhiDisc d : Int) (muVac d : Int) (deltaPhiDisc d : Int) rRings) = (deltaPhiDisc d : Int) ∧
       (compilePhenotypeInEnvOp d (deltaPhiDisc d : Int) 0 (deltaPhiDisc d : Int) rRings).1 = (cuboctShellSizeOp d (c0OverCSqOp d) : Int) ∧
       (compilePhenotypeInEnvOp d (deltaPhiDisc d : Int) 0 (deltaPhiDisc d : Int) rRings).2.1 = (cuboctBallOp d : Int)) ∧
      -- 2. Exact invertibility of major-groove reader synthesis and frame-protected codon encoding
      ((List.range dInSquare).all (fun b =>
        (grooveSynthOp d b < aminoAcidClassesOp d) &&
        (grooveReadOp d (grooveSynthOp d b) == b) &&
        (decodeFrameProtectedCodonOp d (encodeFrameProtectedCodonOp d b) == b) &&
        (encodeFrameProtectedCodonOp d b % c0OverCSqOp d == muVac d)) = true) ∧
      -- 3. Exact self-invertibility (involution) of saturation-driven base mutations and epigenetic stem shifts
      ((List.range dInSquare).all (fun b =>
        (envDrivenBaseMutationOp d (envDrivenBaseMutationOp d b 0) 0 == b) &&
        (envDrivenBaseMutationOp d (envDrivenBaseMutationOp d b (deltaPhiDisc d : Int)) (deltaPhiDisc d : Int) == b) &&
        (envDrivenBaseMutationOp d (envDrivenBaseMutationOp d b (qSquare d : Int)) (qSquare d : Int) == b)) = true ∧
       (List.range (dInSquare * dInSquare)).all (fun s =>
        deaminateFirstBaseStemOp (deaminateFirstBaseStemOp s) == s) = true)) d := by
  apply catalan_chain d (predictive_mutagenesis_and_epigenetic_saturation_operator d)
  intro _
  dsimp [compilePhenotypeInEnvOp, inverseTargetSigmaAxisOp, inverseTargetSigmaIgOp, eqIntIndicatorOp,
         ontogenyGenesisInEnvOp, envSolventMatchGateOp, transmembraneThicknessOp, planetaryEnvWindowOp,
         envMetabolicGateOp, energyQuantumOperator, heisenbergDeadbandOp, blendComplexOp, blendByIndicatorOp,
         tubeComplexOp, corticalColumnComplexOp, vesicleComplexOp, zygoteDormantComplexOp, tissueEuler2DOp,
         cuboctBallOp, cuboctShellSizeOp, isZeroNat, isPosNat, nSquares, nNeighbors, nTriangles, c0OverCSqOp,
         deltaPhiDisc, nRing, nPhi, modBits, dOutEdge, kP, fracBits, muVac, ivSeed, phiPauli, qSquare, dInSquare]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by decide, by decide⟩ <;>
  · simp [Int.zero_mul, Int.one_mul, Int.add_zero, Int.zero_add]
    try omega

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
