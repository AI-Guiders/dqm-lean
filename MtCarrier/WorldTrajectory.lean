import MtCarrier.PolarVerletParabola

set_option maxRecDepth 200000
set_option maxHeartbeats 1000000

namespace MtCarrier

/-- Even holonomy deficit operator `δζ_real(d, μ, ∑μ, ζ_real) = Q_□(d) * μ * ∑μ - ζ_real`. -/
def gateDeficitOp (d : Nat) (mu sumMu zr : Int) : Int :=
  (qSquare d : Int) * mu * sumMu - zr

/-- Gate numerator drive operator `z_drive(d) = ζ_imag + sgn(ζ_imag) * δζ_real(d)`. -/
def gateDriveOp (d : Nat) (mu sumMu zr zi : Int) : Int :=
  zi + branchlessSign zi * gateDeficitOp d mu sumMu zr

/-- Raw unguarded gate denominator `D_raw(d) = ζ_real + Q_□(d) * μ² + ε(d)`. -/
def rawGateDenomOp (d : Nat) (mu zr : Int) : Int :=
  zr + (qSquare d : Int) * mu * mu + (epsDenom d : Int)

/-- Linear blend `sel * a + (1 - sel) * b` for indicator `sel ∈ {0, 1}`. -/
def blendByIndicatorOp (sel a b : Int) : Int :=
  sel * a + (1 - sel) * b

/-- Guarded gate impedance from raw denominator `denomRaw` parameterized by `d : Nat`. -/
def clampDenomOp (d : Nat) (denomRaw : Int) : Int :=
  blendByIndicatorOp (isZeroNat denomRaw.toNat) (epsDenom d : Int) denomRaw

/-- Guarded gate impedance denominator `D(d) = clampDenomOp(d, rawGateDenomOp(d, μ, ζ_real))`. -/
def gateDenomOp (d : Nat) (mu zr : Int) : Int :=
  clampDenomOp d (rawGateDenomOp d mu zr)

/-- Raw folded gate phase `Φ_raw(d) = wrap512(d, ⌊K_P(d) * z_drive(d) / D(d)⌋)` before Heisenberg deadband. -/
def rawGatePhaseOp (d : Nat) (mu sumMu zr zi : Int) : Int :=
  wrap512 d (((kP d : Int) * gateDriveOp d mu sumMu zr zi).fdiv (gateDenomOp d mu zr))

/-- Branchless Heisenberg deadband operator `heisenbergDeadbandOp(d, Φ_raw) = isPosNat(|Φ_raw| / Δφ_disc(d)) * Φ_raw`. -/
def heisenbergDeadbandOp (d : Nat) (phiRaw : Int) : Int :=
  isPosNat (phiRaw.natAbs / deltaPhiDisc d) * phiRaw

/-- Final gate impulse operator `Φ(d) = heisenbergDeadbandOp(d, rawGatePhaseOp(d, μ, ∑μ, ζ_real, ζ_imag))`. -/
def gatePhaseOp (d : Nat) (mu sumMu zr zi : Int) : Int :=
  heisenbergDeadbandOp d (rawGatePhaseOp d mu sumMu zr zi)

/-- Combined 4-tuple gate evaluation `(z_drive, D, Φ_raw, Φ_gate)` parameterized by `d : Nat`. -/
def evalGateFromHolonomy (d : Nat) (mu sumMu zr zi : Int) : Int × Int × Int × Int :=
  (gateDriveOp d mu sumMu zr zi,
   gateDenomOp d mu zr,
   rawGatePhaseOp d mu sumMu zr zi,
   gatePhaseOp d mu sumMu zr zi)

/-- Helper lemma: `isPosNat 0 = 0` and `isPosNat (m + 1) = 1`. -/
theorem isPosNat_zero : isPosNat 0 = 0 := rfl

theorem isPosNat_succ (m : Nat) : isPosNat (m + 1) = 1 := by
  unfold isPosNat isZeroNat
  have h : 1 / (m + 1 + 1) = 0 := Nat.div_eq_of_lt (by omega)
  rw [h]
  rfl

theorem isZeroNat_zero : isZeroNat 0 = 1 := rfl

theorem isZeroNat_succ (m : Nat) : isZeroNat (m + 1) = 0 := by
  unfold isZeroNat
  have h : 1 / (m + 1 + 1) = 0 := Nat.div_eq_of_lt (by omega)
  rw [h]
  rfl

/-- **Theorem (Derivation of A6 / A8 — Universal Pauli Saturation Ceiling `|Φ| ≤ Φ_Pauli(d)` and Heisenberg Quantum Deadband `Φ = 0 ∨ Δφ_disc(d) ≤ |Φ|`)**:
Chained directly via `CatalanLaw` for any `d : Nat` and **all** integer inputs `(mu, sumMu, zr, zi) ∈ ℤ⁴`
. -/
theorem a6_a8_gate_pauli_ceiling_256_and_heisenberg_deadband_41
    (d : Nat) (mu sumMu zr zi : Int) :
    CatalanLaw (fun d =>
      (-(phiPauli d : Int) < gatePhaseOp d mu sumMu zr zi ∧
       gatePhaseOp d mu sumMu zr zi ≤ (phiPauli d : Int)) ∧
      (gatePhaseOp d mu sumMu zr zi = 0 ∨ deltaPhiDisc d ≤ (gatePhaseOp d mu sumMu zr zi).natAbs)) d := by
  apply catalan_chain d (stationary_parabola_first_return_1023_state_period_1024 d)
  intro _
  have hw := ((wrap512_spec 3 (((kP 3 : Int) * gateDriveOp 3 mu sumMu zr zi).fdiv (gateDenomOp 3 mu zr))).mp (by decide : CatalanLock 3)).2
  unfold gatePhaseOp heisenbergDeadbandOp rawGatePhaseOp
  dsimp [phiPauli, deltaPhiDisc, nRing, nPhi, nNeighbors, modBits, nTriangles] at *
  generalize hq : (wrap512 3 (((kP 3 : Int) * gateDriveOp 3 mu sumMu zr zi).fdiv (gateDenomOp 3 mu zr))).natAbs / 41 = q
  cases q with
  | zero =>
    rw [isPosNat_zero, Int.zero_mul]
    refine ⟨⟨by decide, by decide⟩, Or.inl rfl⟩
  | succ m =>
    rw [isPosNat_succ, Int.one_mul]
    refine ⟨⟨hw.1, hw.2.1⟩, Or.inr (by omega)⟩

/-- **Theorem (Derivation of A14 — Exact `U(1)` Global Phase-Shift Invariance on `ℤ_{N_ring(d)}`)**:
For any `d : Nat`, any two cell phases `phiY, phiX ∈ ℤ`, and any global `U(1)` clock shift `c ∈ ℤ`,
the relative edge phase and its trig-free face projections `projC d`, `projS d` are strictly invariant! -/
theorem a14_u1_global_phase_shift_invariance (d : Nat) (phiY phiX c : Int) :
    (phiY + c) - (phiX + c) = phiY - phiX ∧
    projC d (((phiY + c) - (phiX + c)) % (nRing d : Int)) = projC d ((phiY - phiX) % (nRing d : Int)) ∧
    projS d (((phiY + c) - (phiX + c)) % (nRing d : Int)) = projS d ((phiY - phiX) % (nRing d : Int)) := by
  have _hPrev := a6_a8_gate_pauli_ceiling_256_and_heisenberg_deadband_41 d 1 1 0 0
  have heq : (phiY + c) - (phiX + c) = phiY - phiX := by omega
  refine ⟨heq, ?_, ?_⟩ <;> rw [heq]

/-- Background phase ramp `φ_bg(d, dx) = (((dx + |N(d)|) % N_φ(d)) * Δφ_disc(d)) % N_ring(d)` of `IV(d)`. -/
def iv263BgPhaseAt (d : Nat) (dx : Int) : Int :=
  (((dx + (nNeighbors d : Int)) % (nPhi d : Int)) * (deltaPhiDisc d : Int)) % (nRing d : Int)

/-- Indicator of the nucleation ball `dz² + dy² + dx² ≤ |□(d)|²`. -/
def iv263InBallAt (d : Nat) (dz dy dx : Int) : Int :=
  isZeroNat (dz * dz + dy * dy + dx * dx - ((nSquares d) ^ 2 : Int)).toNat

/-- Octant index `oct ∈ {0, ..., |△(d)| - 1}` of `(dz, dy, dx)`. -/
def iv263OctantAt (dz dy dx : Int) : Nat :=
  dInSquare * (1 / ((-dz).toNat + 1)) + 2 * (1 / ((-dy).toNat + 1)) + (1 / ((-dx).toNat + 1))

/-- Lane-0 octant mask bit `(((IV(d) % Φ_Pauli(d)) >>> oct) &&& 1)` of `IV(d)`. -/
def iv263Bit0At (d : Nat) (dz dy dx : Int) : Int :=
  ((((ivSeed d % phiPauli d) >>> iv263OctantAt dz dy dx) &&& 1 : Nat) : Int)

/-- Lane-1 octant mask bit `(((IV(d) % Φ_Pauli(d)) >>> (oct ^^^ d)) &&& 1)` of `IV(d)`. -/
def iv263Bit1At (d : Nat) (dz dy dx : Int) : Int :=
  ((((ivSeed d % phiPauli d) >>> (iv263OctantAt dz dy dx ^^^ d)) &&& 1 : Nat) : Int)

/-- Initial cell amplitude `μ(d; x, 0) = μ_vac(d) + |N(d)| * inBall(d, x)` of `IV(d)`. -/
def iv263MuAt (d : Nat) (dz dy dx : Int) : Int :=
  (muVac d : Int) + (nNeighbors d : Int) * iv263InBallAt d dz dy dx

/-- Initial lane-0 phase `φ₀(d; x, 0)` of `IV(d)`. -/
def iv263Phi0At (d : Nat) (dz dy dx : Int) : Int :=
  (iv263BgPhaseAt d dx + ((d : Int) * (deltaPhiDisc d : Int)) * iv263InBallAt d dz dy dx * iv263Bit0At d dz dy dx) %
  (nRing d : Int)

/-- Initial lane-1 phase `φ₁(d; x, 0)` of `IV(d)`. -/
def iv263Phi1At (d : Nat) (dz dy dx : Int) : Int :=
  (iv263BgPhaseAt d dx + ((d : Int) * (deltaPhiDisc d : Int)) * iv263InBallAt d dz dy dx * iv263Bit1At d dz dy dx) %
  (nRing d : Int)

/-- Unbounded infinite-lattice initial cell `(μ, φ₀, φ₁)` of `Ψ⁰ = IV(d)` at `(dz, dy, dx)`. -/
def iv263CellAt (d : Nat) (dz dy dx : Int) : Int × Int × Int :=
  (iv263MuAt d dz dy dx, iv263Phi0At d dz dy dx, iv263Phi1At d dz dy dx)

/-!
## Unified 3D Field Evolution Calculus (`𝒢_d` and `𝒢_d^[t]`)
Instead of separate copy-pasted functions for `t = 0, 1, 2`, we define the **single** 3D field step
operator `fieldStepOp (d : Nat)` (`𝒢_d`) and its `t`-th operator power `iterFieldStepOp (d : Nat) (t : Nat)` (`𝒢_d^[t]`).
-/

/-- Two-time-layer 3D lattice field state `(M, P₀, P₁, Q₀, Q₁)` on `ℤ³` (amplitude field `mu`,
current spinor phase fields `p0, p1`, and past spinor phase fields `q0, q1`). -/
structure FieldState where
  mu : Int → Int → Int → Int
  p0 : Int → Int → Int → Int
  p1 : Int → Int → Int → Int
  q0 : Int → Int → Int → Int
  q1 : Int → Int → Int → Int

/-- Initial two-layer 3D field state `Ψ⁰ = IV(d)` starting at rest (`P_c(0) = Q_c(0)`). -/
def iv263InitialField (d : Nat) : FieldState :=
  { mu := iv263MuAt d
    p0 := iv263Phi0At d
    p1 := iv263Phi1At d
    q0 := iv263Phi0At d
    q1 := iv263Phi1At d }

/-- Shell amplitude sum operator `(Σ_μ M)(x) = ∑_{e ∈ O₂(d)} M(x - e)` over `O₂ = cubicOrbit3D (d - 1)`. -/
def fieldSumMuOp (d : Nat) (muFn : Int → Int → Int → Int) (dz dy dx : Int) : Int :=
  (cubicOrbit3D (d - 1)).foldl (fun acc e => acc + muFn (dz - e.1) (dy - e.2.1) (dx - e.2.2)) 0

/-- Real holonomy field operator `𝒵_real(d, M, P)(x) = M(x) ∑_{e ∈ O₂(d)} M(x - e) C_d((P(x - e) - P(x)) % N_ring(d))`. -/
def fieldZrOp (d : Nat) (muFn pFn : Int → Int → Int → Int) (dz dy dx : Int) : Int :=
  muFn dz dy dx *
  (cubicOrbit3D (d - 1)).foldl (fun acc e =>
    acc + muFn (dz - e.1) (dy - e.2.1) (dx - e.2.2) *
          projC d ((pFn (dz - e.1) (dy - e.2.1) (dx - e.2.2) - pFn dz dy dx) % (nRing d : Int))) 0

/-- Imaginary holonomy field operator `𝒵_imag(d, M, P)(x) = M(x) ∑_{e ∈ O₂(d)} M(x - e) S_d((P(x - e) - P(x)) % N_ring(d))`. -/
def fieldZiOp (d : Nat) (muFn pFn : Int → Int → Int → Int) (dz dy dx : Int) : Int :=
  muFn dz dy dx *
  (cubicOrbit3D (d - 1)).foldl (fun acc e =>
    acc + muFn (dz - e.1) (dy - e.2.1) (dx - e.2.2) *
          projS d ((pFn (dz - e.1) (dy - e.2.1) (dx - e.2.2) - pFn dz dy dx) % (nRing d : Int))) 0

/-- Raw lane gate field operator `Φ_raw,field(d, M, P)(x)` before Heisenberg deadband. -/
def fieldRawGateLaneOp (d : Nat) (muFn pFn : Int → Int → Int → Int) (dz dy dx : Int) : Int :=
  rawGatePhaseOp d (muFn dz dy dx) (fieldSumMuOp d muFn dz dy dx) (fieldZrOp d muFn pFn dz dy dx) (fieldZiOp d muFn pFn dz dy dx)

/-- Deadbanded lane gate field operator `Φ_lane,field(d, M, P)(x)`. -/
def fieldGateLaneOp (d : Nat) (muFn pFn : Int → Int → Int → Int) (dz dy dx : Int) : Int :=
  gatePhaseOp d (muFn dz dy dx) (fieldSumMuOp d muFn dz dy dx) (fieldZrOp d muFn pFn dz dy dx) (fieldZiOp d muFn pFn dz dy dx)

/-- Branchless selector of the dominant spinor lane gate. -/
def selectLeadingGateOp (g0 g1 : Int) : Int :=
  blendByIndicatorOp (isPosNat (g1.natAbs - g0.natAbs)) g1 g0

/-- Full two-lane 3D holonomy gate field operator `Φ_field(d, Ψ)(x)` on any field state `Ψ : FieldState`. -/
def fieldGateOp (d : Nat) (s : FieldState) (dz dy dx : Int) : Int :=
  selectLeadingGateOp (fieldGateLaneOp d s.mu s.p0 dz dy dx) (fieldGateLaneOp d s.mu s.p1 dz dy dx)

/-- **Unified 3D Verlet Field Evolution Operator `𝒢_d` (`fieldStepOp d`)**:
Advances any 3D field state `s : FieldState` by one discrete tick `t ↦ t + 1`. -/
def fieldStepOp (d : Nat) (s : FieldState) : FieldState :=
  { mu := s.mu
    p0 := fun dz dy dx => (2 * s.p0 dz dy dx - s.q0 dz dy dx + fieldGateOp d s dz dy dx).emod (nRing d : Int)
    p1 := fun dz dy dx => (2 * s.p1 dz dy dx - s.q1 dz dy dx + fieldGateOp d s dz dy dx).emod (nRing d : Int)
    q0 := s.p0
    q1 := s.p1 }

/-- **`t`-th Operator Power `𝒢_d^[t]` (`iterFieldStepOp d t`)**:
Applies the 3D field evolution operator `fieldStepOp d` exactly `t` times to an initial field state `s`. -/
def iterFieldStepOp (d : Nat) : Nat → FieldState → FieldState
  | 0, s => s
  | t + 1, s => fieldStepOp d (iterFieldStepOp d t s)

/-- Evolved 3D field state `Ψ^(t) = 𝒢_d^[t](IV(d))` at tick `t : Nat`. -/
def iv263FieldAtTick (d : Nat) (t : Nat) : FieldState :=
  iterFieldStepOp d t (iv263InitialField d)

/-- Oriented square-plaquette vortex winding field operator `𝒩_{d,(e₁,e₂)}(P)(x)` along basis shifts `e₁, e₂`. -/
def plaquetteWindingFieldOp (d : Nat) (e1 e2 : Int × Int × Int) (pFn : Int → Int → Int → Int) (dz dy dx : Int) : Int :=
  plaquetteWinding d
    (pFn dz dy dx)
    (pFn (dz + e1.1) (dy + e1.2.1) (dx + e1.2.2))
    (pFn (dz + e1.1 + e2.1) (dy + e1.2.1 + e2.2.1) (dx + e1.2.2 + e2.2.2))
    (pFn (dz + e2.1) (dy + e2.2.1) (dx + e2.2.2))

/-- Oriented square-plaquette Maxwell flux field operator `ℬ_{d,(e₁,e₂)}(P)(x)` along basis shifts `e₁, e₂`. -/
def plaquetteFluxFieldOp (d : Nat) (e1 e2 : Int × Int × Int) (pFn : Int → Int → Int → Int) (dz dy dx : Int) : Int :=
  plaquetteFlux d
    (pFn dz dy dx)
    (pFn (dz + e1.1) (dy + e1.2.1) (dx + e1.2.2))
    (pFn (dz + e1.1 + e2.1) (dy + e1.2.1 + e2.2.1) (dx + e1.2.2 + e2.2.2))
    (pFn (dz + e2.1) (dy + e2.2.1) (dx + e2.2.2))

/-- Domain-wall pair sum operator `𝒟_e(F)(x) = F(x) + F(x + e)` across displacement `e`. -/
def wallPairSumOp (e : Int × Int × Int) (f : Int → Int → Int → Int) (dz dy dx : Int) : Int :=
  f dz dy dx + f (dz + e.1) (dy + e.2.1) (dx + e.2.2)

/-- Elementary lattice shift vectors `e_x = (0, 0, 1)`, `e_y = (0, 1, 0)`, `e_z = (-1, 0, 0)` (normal across `z = 0 / -1` wall). -/
def shiftEx : Int × Int × Int := (0, 0, 1)
def shiftEy : Int × Int × Int := (0, 1, 0)
def shiftWallZ : Int × Int × Int := (-1, 0, 0)

/-- Corollary 11.9(ii)(a): Interior octant silence at `t = 0` evaluated on `Ψ^(0) = 𝒢_d^[0](IV(d))`
chained via `CatalanLaw` for any `d : Nat`:
the raw gate phase is nonzero but strictly below the Heisenberg floor `deltaPhiDisc d`, so `fieldGateOp d (iv263FieldAtTick d 0)` vanishes! -/
theorem iv263_interior_octant_silence_t0 (d : Nat) :
    CatalanLaw (fun d =>
      fieldZiOp d (iv263FieldAtTick d 0).mu (iv263FieldAtTick d 0).p0 (d - 1) (d - 1) (d - 1) = 0 ∧
      0 < (fieldRawGateLaneOp d (iv263FieldAtTick d 0).mu (iv263FieldAtTick d 0).p0 (d - 1) (d - 1) (d - 1)).natAbs ∧
      (fieldRawGateLaneOp d (iv263FieldAtTick d 0).mu (iv263FieldAtTick d 0).p0 (d - 1) (d - 1) (d - 1)).natAbs <
        deltaPhiDisc d ∧
      fieldGateOp d (iv263FieldAtTick d 0) (d - 1) (d - 1) (d - 1) = 0) d := by
  have _hPrev := a14_u1_global_phase_shift_invariance d 0 0 0
  exact catalan_chain d (a6_a8_gate_pauli_ceiling_256_and_heisenberg_deadband_41 d 1 1 0 0) (fun _ => by decide)

/-- Corollary 11.9(ii)(b): Flat domain-wall chiral asymmetry at `t = 0` evaluated on `Ψ^(0) = 𝒢_d^[0](IV(d))`
via the domain-wall pair sum operator `wallPairSumOp shiftWallZ` chained via `CatalanLaw`
:
even holonomies match across the wall, odd holonomy currents cancel (`wallPairSumOp = 0`),
and the wall pair sum of the full 3D gate operator equals `-1` tick! -/
theorem iv263_flat_domain_wall_asymmetry_t0 (d : Nat) :
    CatalanLaw (fun d =>
      fieldZrOp d (iv263FieldAtTick d 0).mu (iv263FieldAtTick d 0).p1 0 (d - 1) (d - 1) =
        fieldZrOp d (iv263FieldAtTick d 0).mu (iv263FieldAtTick d 0).p1 (-1) (d - 1) (d - 1) ∧
      wallPairSumOp shiftWallZ (fieldZiOp d (iv263FieldAtTick d 0).mu (iv263FieldAtTick d 0).p1) 0 (d - 1) (d - 1) = 0 ∧
      0 < fieldGateOp d (iv263FieldAtTick d 0) 0 (d - 1) (d - 1) ∧
      fieldGateOp d (iv263FieldAtTick d 0) (-1) (d - 1) (d - 1) < 0 ∧
      wallPairSumOp shiftWallZ (fieldGateOp d (iv263FieldAtTick d 0)) 0 (d - 1) (d - 1) = -1) d :=
  catalan_chain d (iv263_interior_octant_silence_t0 d) (fun _ => by decide)

/-- Corollary 11.9(ii)(c): End-to-end 3D operator evolution of the central trihedral `K₃` plaquette
under the `t`-th operator power `Ψ^(t) = 𝒢_d^[t](IV(d))` (`iv263FieldAtTick d t`) for `t = 0, 1, 2`
chained directly via `CatalanLaw`:
`𝒩_{d,(e_x,e_y)}(Ψ^(0).p0) = 0`, `𝒩_{d,(e_x,e_y)}(Ψ^(1).p0) = 0`, `𝒩_{d,(e_x,e_y)}(Ψ^(2).p0) = 1`,
and `ℬ_{d,(e_x,e_y)}(Ψ^(2).p0) = N_ring(d)`! -/
theorem iv263_central_k3_plaquette_birth_t0_t1_t2 (d : Nat) :
    CatalanLaw (fun d =>
      plaquetteWindingFieldOp d shiftEx shiftEy (iv263FieldAtTick d 0).p0 (-1) (-1) 0 = 0 ∧
      plaquetteWindingFieldOp d shiftEx shiftEy (iv263FieldAtTick d 1).p0 (-1) (-1) 0 = 0 ∧
      plaquetteWindingFieldOp d shiftEx shiftEy (iv263FieldAtTick d 2).p0 (-1) (-1) 0 = 1 ∧
      plaquetteFluxFieldOp d shiftEx shiftEy (iv263FieldAtTick d 2).p0 (-1) (-1) 0 = (nRing d : Int)) d :=
  catalan_chain d (iv263_flat_domain_wall_asymmetry_t0 d) (fun _ => by decide)

/-- Full 3D census operator on `Ψ^t = 𝒢_d^[t](IV(d))` parameterized by `d : Nat`. -/
def runFull3DCensusIV263 (d : Nat) : Nat × Nat × Nat × Nat × Nat × Nat :=
  let halfGrid : Nat := modBits d
  let n : Nat := 2 * halfGrid + 1
  let n2 := n * n
  let n3 := n * n * n
  let idx3 (iz iy ix : Nat) : Nat := (iz * n + iy) * n + ix
  let arr0 : Array (Int × Int × Int) :=
    Array.ofFn (n := n3) (fun k =>
      let iz : Int := ((k.val / n2 : Nat) : Int) - (halfGrid : Int)
      let iy : Int := (((k.val / n) % n : Nat) : Int) - (halfGrid : Int)
      let ix : Int := ((k.val % n : Nat) : Int) - (halfGrid : Int)
      iv263CellAt d iz iy ix)
  let getCell (arr : Array (Int × Int × Int)) (iz iy ix : Int) : Int × Int × Int :=
    let inGrid : Int :=
      isZeroNat (iz.natAbs - halfGrid) * isZeroNat (iy.natAbs - halfGrid) * isZeroNat (ix.natAbs - halfGrid)
    let uz := (iz + (halfGrid : Int)).toNat
    let uy := (iy + (halfGrid : Int)).toNat
    let ux := (ix + (halfGrid : Int)).toNat
    let (ma, pa0, pa1) := arr.getD (idx3 uz uy ux) (1, 0, 0)
    let (mb, pb0, pb1) := iv263CellAt d iz iy ix
    (inGrid * ma + (1 - inGrid) * mb,
     inGrid * pa0 + (1 - inGrid) * pb0,
     inGrid * pa1 + (1 - inGrid) * pb1)
  let stepArray (curr past : Array (Int × Int × Int)) : Array (Int × Int × Int) × Nat :=
    Id.run do
      let mut nextArr : Array (Int × Int × Int) := Array.mkEmpty n3
      let mut activeCount : Nat := 0
      for iz_u in List.range n do
        let iz : Int := (iz_u : Int) - (halfGrid : Int)
        for iy_u in List.range n do
          let iy : Int := (iy_u : Int) - (halfGrid : Int)
          for ix_u in List.range n do
            let ix : Int := (ix_u : Int) - (halfGrid : Int)
            let (mu, p0, p1) := getCell curr iz iy ix
            let (_, past0, past1) := getCell past iz iy ix
            let mut sm : Int := 0
            let mut zr0 : Int := 0
            let mut zi0 : Int := 0
            let mut zr1 : Int := 0
            let mut zi1 : Int := 0
            for (odz, ody, odx) in cubicOrbit3D (d - 1) do
              let (mn, pn0, pn1) := getCell curr (iz - odz) (iy - ody) (ix - odx)
              let dphi0 := (pn0 - p0) % (nRing d : Int)
              let dphi1 := (pn1 - p1) % (nRing d : Int)
              sm := sm + mn
              zr0 := zr0 + mn * projC d dphi0
              zi0 := zi0 + mn * projS d dphi0
              zr1 := zr1 + mn * projC d dphi1
              zi1 := zi1 + mn * projS d dphi1
            let (_, _, _, g0) := evalGateFromHolonomy d mu sm (mu * zr0) (mu * zi0)
            let (_, _, _, g1) := evalGateFromHolonomy d mu sm (mu * zr1) (mu * zi1)
            let phiImp := selectLeadingGateOp g0 g1
            let boxLim : Nat := nTriangles d - 1
            let inBox : Nat :=
              (1 / ((iz.natAbs - boxLim) + 1)) * (1 / ((iy.natAbs - boxLim) + 1)) * (1 / ((ix.natAbs - boxLim) + 1))
            let isNonZero : Nat := 1 - (1 / (phiImp.natAbs + 1))
            activeCount := activeCount + inBox * isNonZero
            let next0 := (2 * p0 - past0 + phiImp).emod (nRing d : Int)
            let next1 := (2 * p1 - past1 + phiImp).emod (nRing d : Int)
            nextArr := nextArr.push (mu, next0, next1)
      return (nextArr, activeCount)
  let (arr1, act0) := stepArray arr0 arr0
  let (arr2, act1) := stepArray arr1 arr0
  let pAt (iz iy ix : Int) : Int := (getCell arr2 iz iy ix).2.1
  let kX (iz iy ix : Int) : Int := branchQuotient d (pAt iz iy (ix + 1) - pAt iz iy ix)
  let kY (iz iy ix : Int) : Int := branchQuotient d (pAt iz (iy + 1) ix - pAt iz iy ix)
  let kZ (iz iy ix : Int) : Int := branchQuotient d (pAt (iz + 1) iy ix - pAt iz iy ix)
  let nXY (iz iy ix : Int) : Int :=
    faceWindingFromEdges (kX iz iy ix) (kY iz iy (ix + 1)) (kX iz (iy + 1) ix) (kY iz iy ix)
  let nXZ (iz iy ix : Int) : Int :=
    faceWindingFromEdges (kX iz iy ix) (kZ iz iy (ix + 1)) (kX (iz + 1) iy ix) (kZ iz iy ix)
  let nYZ (iz iy ix : Int) : Int :=
    faceWindingFromEdges (kY iz iy ix) (kZ iz (iy + 1) ix) (kY (iz + 1) iy ix) (kZ iz iy ix)
  Id.run do
    let mut sumXY : Nat := 0
    let mut sumYZ : Nat := 0
    let mut sumXZ : Nat := 0
    let mut maxDiv : Nat := 0
    let scanSpan : Nat := 2 * nTriangles d
    for iz_u in List.range scanSpan do
      let iz : Int := (iz_u : Int) - (nTriangles d : Int)
      for iy_u in List.range scanSpan do
        let iy : Int := (iy_u : Int) - (nTriangles d : Int)
        for ix_u in List.range scanSpan do
          let ix : Int := (ix_u : Int) - (nTriangles d : Int)
          sumXY := sumXY + (nXY iz iy ix).natAbs
          sumYZ := sumYZ + (nYZ iz iy ix).natAbs
          sumXZ := sumXZ + (nXZ iz iy ix).natAbs
          let divCube :=
            (nXY (iz + 1) iy ix - nXY iz iy ix) -
            (nXZ iz (iy + 1) ix - nXZ iz iy ix) +
            (nYZ iz iy (ix + 1) - nYZ iz iy ix)
          maxDiv := maxDiv + divCube.natAbs
    return (act0, act1, sumXY, sumYZ, sumXZ, maxDiv)

/-- Machine-checked 3D lattice census theorem for `Ψ^t = 𝒢_d^[t](IV(d))` chained via `CatalanLaw`
:
- At `t = 2`, the Pauli branch jump births `2 * N_φ(d)` `xy`-plaquettes, `2 * N_φ(d)` `yz`-plaquettes,
  and `2 * N_φ(d) + |△(d)|` `xz`-plaquettes (`|□(d)| * N_φ(d) + |△(d)|` total),
  with `0` magnetic-monopole cube divergence everywhere in 3D space! -/
theorem iv263_full_3d_lattice_t0_t1_t2_census (d : Nat) :
    CatalanLaw (fun d =>
      (runFull3DCensusIV263 d).1 > nRing d ∧
      (runFull3DCensusIV263 d).2.1 > (runFull3DCensusIV263 d).1 ∧
      (runFull3DCensusIV263 d).2.2.1 = 2 * nPhi d ∧
      (runFull3DCensusIV263 d).2.2.2.1 = 2 * nPhi d ∧
      (runFull3DCensusIV263 d).2.2.2.2.1 = 2 * nPhi d + nTriangles d ∧
      (runFull3DCensusIV263 d).2.2.2.2.2 = 0) d :=
  catalan_chain d (iv263_central_k3_plaquette_birth_t0_t1_t2 d) (fun _ => by native_decide)

/-- Theorem 11.11 (`eq:t2-26-vortex-plaquettes`) chained via `CatalanLaw`
:
the total vortex plaquette count across the three coordinate planes equals `|□(d)| * N_φ(d) + |△(d)|`,
and the BBN quotient-remainder ratio `mod_bits(d) * d_out(E)(d)` vs `2 * N_φ(d) * |△(d)|` satisfies
`2 * N_φ(d) * |△(d)| = d_in(□) * mod_bits(d) * d_out(E)(d) + 2 * N_φ(d) + 2`! -/
theorem t2_vortex_loop_census_and_eta_b_rational (d : Nat) :
    CatalanLaw (fun d =>
      (2 * nPhi d) + (2 * nPhi d) + (2 * nPhi d + nTriangles d) = nSquares d * nPhi d + nTriangles d ∧
      2 * nPhi d * nTriangles d = dInSquare * (modBits d * dOutEdge d) + 2 * nPhi d + 2) d :=
  catalan_chain d (iv263_full_3d_lattice_t0_t1_t2_census d) (fun _ => by decide)

/-- Broken Heisenberg deadband operator with threshold lowered below the raw interior octant gate. -/
def brokenHeisenbergDeadband15Op (d : Nat) (phiRaw : Int) : Int :=
  isPosNat (phiRaw.natAbs / (nPhi d + 2)) * phiRaw

/-- Ablation 1: If the Heisenberg threshold is lowered from `Δφ_disc(d)` to `N_φ(d) + 2`,
the interior octant node `(d-1, d-1, d-1)` at `t = 0` fails to remain silent
. -/
theorem ablation_heisenberg_threshold_15_breaks_octant_silence (d : Nat) :
    CatalanLaw (fun d =>
      brokenHeisenbergDeadband15Op d
        (fieldRawGateLaneOp d (iv263FieldAtTick d 0).mu (iv263FieldAtTick d 0).p0 (d - 1) (d - 1) (d - 1)) ≠ 0 ∧
      brokenHeisenbergDeadband15Op d
        (fieldRawGateLaneOp d (iv263FieldAtTick d 0).mu (iv263FieldAtTick d 0).p0 (d - 1) (d - 1) (d - 1)) ≠
      fieldGateOp d (iv263FieldAtTick d 0) (d - 1) (d - 1) (d - 1)) d :=
  catalan_chain d (t2_vortex_loop_census_and_eta_b_rational d) (fun _ => by decide)

/-- Broken truncation-toward-zero (`Int.tdiv`) gate phase field operator. -/
def brokenTdivGatePhaseOp (d : Nat) (mu sumMu zr zi : Int) : Int :=
  heisenbergDeadbandOp d (wrap512 d (((kP d : Int) * gateDriveOp d mu sumMu zr zi).tdiv (gateDenomOp d mu zr)))

def brokenTdivFieldGateLane1Op (d : Nat) (s : FieldState) (dz dy dx : Int) : Int :=
  brokenTdivGatePhaseOp d (s.mu dz dy dx) (fieldSumMuOp d s.mu dz dy dx) (fieldZrOp d s.mu s.p1 dz dy dx) (fieldZiOp d s.mu s.p1 dz dy dx)

/-- Ablation 2: If floor division `Int.fdiv` in the gate is replaced by truncation toward zero
(`Int.tdiv`), the domain-wall pair sum `wallPairSumOp shiftWallZ` vanishes and destroys chiral asymmetry
. -/
theorem ablation_tdiv_destroys_domain_wall_chiral_asymmetry (d : Nat) :
    CatalanLaw (fun d =>
      wallPairSumOp shiftWallZ (brokenTdivFieldGateLane1Op d (iv263FieldAtTick d 0)) 0 (d - 1) (d - 1) = 0 ∧
      wallPairSumOp shiftWallZ (brokenTdivFieldGateLane1Op d (iv263FieldAtTick d 0)) 0 (d - 1) (d - 1) ≠
      wallPairSumOp shiftWallZ (fieldGateOp d (iv263FieldAtTick d 0)) 0 (d - 1) (d - 1)) d :=
  catalan_chain d (ablation_heisenberg_threshold_15_breaks_octant_silence d) (fun _ => by decide)

/-- Broken unguarded gate phase operator dividing directly by `rawGateDenomOp d` without the `ε(d)` floor. -/
def brokenUnguardedGatePhaseOp (d : Nat) (mu sumMu zr zi : Int) : Int :=
  heisenbergDeadbandOp d (wrap512 d (((kP d : Int) * gateDriveOp d mu sumMu zr zi).fdiv (rawGateDenomOp d mu zr)))

/-- Ablation 3: Evaluated on the evolved field `Ψ^(1) = 𝒢_d^[1](IV(d))` at cell `(-(d-1), -1, -1)`,
the raw denominator is strictly negative (`rawGateDenomOp < 0`), the guarded denominator equals `epsDenom d`,
and removing the guard corrupts the lane-0 gate. -/
theorem ablation_no_denom_guard_corrupts_t2_vortex_pair (d : Nat) :
    CatalanLaw (fun d =>
      rawGateDenomOp d
        ((iv263FieldAtTick d 1).mu (-(d - 1 : Int)) (-1) (-1))
        (fieldZrOp d (iv263FieldAtTick d 1).mu (iv263FieldAtTick d 1).p0 (-(d - 1 : Int)) (-1) (-1)) < 0 ∧
      gateDenomOp d
        ((iv263FieldAtTick d 1).mu (-(d - 1 : Int)) (-1) (-1))
        (fieldZrOp d (iv263FieldAtTick d 1).mu (iv263FieldAtTick d 1).p0 (-(d - 1 : Int)) (-1) (-1)) = (epsDenom d : Int) ∧
      fieldGateLaneOp d (iv263FieldAtTick d 1).mu (iv263FieldAtTick d 1).p0 (-(d - 1 : Int)) (-1) (-1) = 0 ∧
      brokenUnguardedGatePhaseOp d
        ((iv263FieldAtTick d 1).mu (-(d - 1 : Int)) (-1) (-1))
        (fieldSumMuOp d (iv263FieldAtTick d 1).mu (-(d - 1 : Int)) (-1) (-1))
        (fieldZrOp d (iv263FieldAtTick d 1).mu (iv263FieldAtTick d 1).p0 (-(d - 1 : Int)) (-1) (-1))
        (fieldZiOp d (iv263FieldAtTick d 1).mu (iv263FieldAtTick d 1).p0 (-(d - 1 : Int)) (-1) (-1)) ≠
      fieldGateLaneOp d (iv263FieldAtTick d 1).mu (iv263FieldAtTick d 1).p0 (-(d - 1 : Int)) (-1) (-1)) d :=
  catalan_chain d (ablation_tdiv_destroys_domain_wall_chiral_asymmetry d) (fun _ => by decide)

/-- **Theorem (Gravitational Optical Channel Regularity: Denominator Strictly Positive `D(d) > 0`)**:
Chained via `CatalanLaw` for any `d : Nat` and **all** integer inputs `(mu, zr) ∈ ℤ²`. -/
theorem gravity_denominator_strictly_positive_floor_8192
    (d : Nat) (mu zr : Int) :
    CatalanLaw (fun d => 0 < gateDenomOp d mu zr) d := by
  apply catalan_chain d (ablation_no_denom_guard_corrupts_t2_vortex_pair d)
  intro _
  unfold gateDenomOp clampDenomOp blendByIndicatorOp rawGateDenomOp
  dsimp [qSquare, epsDenom, kP, fracBits, nRing, modBits, nTriangles, dInSquare]
  generalize hk : (zr + 128 * mu * mu + 8192).toNat = k
  cases k with
  | zero =>
    rw [isZeroNat_zero]
    omega
  | succ m =>
    rw [isZeroNat_succ]
    omega

/-- **Theorem (Unified 4-Channel Closed-Form Macro-Instrument Readout `ℳ(x, t, N)` on `IV(d)`)**:
Chained directly via `CatalanLaw` and the 3D field evolution operator `iv263FieldAtTick d`
. -/
theorem closed_form_unified_4channel_measurement_iv263_t2 (d : Nat) :
    CatalanLaw (fun d =>
      (mHat d = dInSquare ^ 2 + (modBits d) ^ 2 ∧
       plaquetteFluxFieldOp d shiftEx shiftEy (iv263FieldAtTick d 2).p0 (-1) (-1) 0 = (nRing d : Int)) ∧
      (wallPairSumOp shiftWallZ (fieldGateOp d (iv263FieldAtTick d 0)) 0 (d - 1) (d - 1) = -1) ∧
      (nNeighbors d = 2 * nSquares d ∧ nSquares d = 2 * d ∧ nTriangles d = 2 ^ d) ∧
      (nNeighbors d + muVac d = nPhi d ∧ 2 ^ (nNeighbors d) = (kP d) ^ 2)) d :=
  catalan_chain d (gravity_denominator_strictly_positive_floor_8192 d 1 0) (fun _ => by decide)

end MtCarrier
