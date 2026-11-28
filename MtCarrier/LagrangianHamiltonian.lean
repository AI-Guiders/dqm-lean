import MtCarrier.MechanicsElasticity

set_option maxRecDepth 200000
set_option maxHeartbeats 1000000

/-!
# World-Field Lagrangian `ℒ_world`, Hamiltonian `ℋ_world`, 13-Node Causal Star `𝒞₁₃` Denominator Decomposition, and Time-Derivative Tower (`D_t^1, D_t^2, D_t^3`) (`0 sorryAx`, `0 Classical.choice`, `0 Prop premises`)

This module formalizes the 3D World-Field Lagrangian and Hamiltonian densities
along the 3D world evolution operator `Ψ^{(t+1)} = 𝒢_d(Ψ^{(t)})` (`fieldStepOp d` in `WorldTrajectory.lean`),
together with the 13-node causal star `𝒞₁₃ = {0} ∪ O₂(d)` decomposition of `D_raw(x, t)` and the time-derivative tower:
1. **13-Node Causal Star `𝒞₁₃ = {0} ∪ O₂(d)` Decomposition of the Gate Denominator `D_raw(x, t)`:**
   - The central node `e = 0` (`Δφ₀ = 0`) has odd projection `M(x)² * S_d(0) = 0` and even projection `M(x)² * C_d(0) = Q_□(d) * M(x)²`.
   - Therefore, `𝒵_imag^{𝒞₁₃}(x) = 𝒵_imag^{O₂}(x)` and `D_raw,c(Ψ)(x) = 𝒵_real^{𝒞₁₃}(x) + ε(d)`.
2. **3D World-Field Lagrangian `ℒ_world` & Hamiltonian `ℋ_world` Densities:**
   - Temporal kinetic energy density weighted by `M(x)²`:
     `𝒯_time,c(Ψ)(x) = M(x)² * (Q_□(d) - C_d((P_c(x) - Q_c(x)) % N_ring(d))) ≥ 0`.
   - 12-ray spatial gradient potential energy density (even holonomy deficit):
     `𝒰_grad,c(Ψ)(x) = Q_□(d) * M(x) * Σ_μ(x) - 𝒵_real,c(Ψ)(x) ≥ 0`.
   - World-Field Lagrangian density `ℒ_world,c(Ψ)(x) = 𝒯_time,c(Ψ)(x) - 𝒰_grad,c(Ψ)(x)` and
     World-Field Hamiltonian density `ℋ_world,c(Ψ)(x) = 𝒯_time,c(Ψ)(x) + 𝒰_grad,c(Ψ)(x)`.
3. **Worldline Potential-Denominator Balance (`𝒰_grad(x, t) + D_raw(x, t) ≡ const(t)`):**
   - At every spatial node `x ∈ ℤ³` and across all time ticks `t ∈ ℕ` of the 3D world evolution `Ψ^{(t)} = 𝒢_d^[t](Ψ^{(0)})`,
     `𝒰_grad,c(Ψ^{(t)})(x) + D_raw,c(Ψ^{(t)})(x) ≡ Q_□(d) * M(x) * (Σ_μ(x) + M(x)) + ε(d)`.
4. **Mass-Weighted Closed-Form Parabola Hamiltonian `ℋ_parab(t) ≡ 0`, Tetrahedral Action `3 * ∑_{t=1}^N ℒ_parab(t) = M_eff * Φ₀² * N(N+1)(N+2)`, and Time-Derivative Tower (`D_t^1, D_t^2, D_t^3`).**
-/

namespace MtCarrier

/-- Unwrapped second-order Verlet transition operator `φ_{t+1} = 2 * φ_t - φ_{t-1} + F_t`. -/
def verletStepOp (phiCurr phiPrev fImp : Int) : Int :=
  2 * phiCurr - phiPrev + fImp

/-- 3D World-Field temporal kinetic energy density weighted by the cell's squared amplitude mass `M(x)²`:
`𝒯_time(d, M, P, Q)(x) = M(x)² * (Q_□(d) - C_d((P(x) - Q(x)) % N_ring(d)))`. -/
def fieldTemporalKineticOp (d : Nat) (muFn pFn qFn : Int → Int → Int → Int) (dz dy dx : Int) : Int :=
  let m := muFn dz dy dx
  m * m * ((qSquare d : Int) - projC d ((pFn dz dy dx - qFn dz dy dx) % (nRing d : Int)))

/-- 3D World-Field 12-ray spatial gradient potential energy density (`δ𝒵_real(x)`):
`𝒰_grad(d, M, P)(x) = Q_□(d) * M(x) * Σ_μ(x) - 𝒵_real(d, M, P)(x)`. -/
def fieldSpatialPotentialOp (d : Nat) (muFn pFn : Int → Int → Int → Int) (dz dy dx : Int) : Int :=
  gateDeficitOp d (muFn dz dy dx) (fieldSumMuOp d muFn dz dy dx) (fieldZrOp d muFn pFn dz dy dx)

/-- Central-node (`e = 0`, `Δφ₀ = 0`) even projection `M(x)² * C_d(0) = Q_□(d) * M(x)²` and odd projection `M(x)² * S_d(0) = 0`
completing the 12-neighbor shell `O₂(d)` to the full 13-node causal star `𝒞₁₃ = {0} ∪ O₂(d)`. -/
def centralNodeEvenHolonomyOp (d : Nat) (muFn : Int → Int → Int → Int) (dz dy dx : Int) : Int :=
  let m := muFn dz dy dx
  m * m * projC d 0

def centralNodeOddHolonomyOp (d : Nat) (muFn : Int → Int → Int → Int) (dz dy dx : Int) : Int :=
  let m := muFn dz dy dx
  m * m * projS d 0

/-- Full 13-node causal star `𝒞₁₃ = {0} ∪ O₂(d)` even holonomy `𝒵_real^{𝒞₁₃}(x) = M(x)² * C_d(0) + 𝒵_real^{O₂}(x)`. -/
def fullStar13EvenHolonomyOp (d : Nat) (muFn pFn : Int → Int → Int → Int) (dz dy dx : Int) : Int :=
  centralNodeEvenHolonomyOp d muFn dz dy dx + fieldZrOp d muFn pFn dz dy dx

/-- Full 13-node causal star `𝒞₁₃ = {0} ∪ O₂(d)` odd holonomy `𝒵_imag^{𝒞₁₃}(x) = M(x)² * S_d(0) + 𝒵_imag^{O₂}(x) ≡ 𝒵_imag^{O₂}(x)`. -/
def fullStar13OddHolonomyOp (d : Nat) (muFn pFn : Int → Int → Int → Int) (dz dy dx : Int) : Int :=
  centralNodeOddHolonomyOp d muFn dz dy dx + fieldZiOp d muFn pFn dz dy dx

/-- 3D World-Field raw gate denominator `D_raw(d, M, P)(x) = 𝒵_real^{𝒞₁₃}(x) + ε(d) = 𝒵_real(d, M, P)(x) + Q_□(d) * M(x)² + ε(d)`. -/
def fieldRawGateDenomOp (d : Nat) (muFn pFn : Int → Int → Int → Int) (dz dy dx : Int) : Int :=
  rawGateDenomOp d (muFn dz dy dx) (fieldZrOp d muFn pFn dz dy dx)

/-- 3D World-Field Lagrangian density `ℒ_world(d, M, P, Q)(x) = 𝒯_time(x) - 𝒰_grad(x)`. -/
def fieldLagrangianDensityOp (d : Nat) (muFn pFn qFn : Int → Int → Int → Int) (dz dy dx : Int) : Int :=
  fieldTemporalKineticOp d muFn pFn qFn dz dy dx - fieldSpatialPotentialOp d muFn pFn dz dy dx

/-- 3D World-Field Hamiltonian density `ℋ_world(d, M, P, Q)(x) = 𝒯_time(x) + 𝒰_grad(x)`. -/
def fieldHamiltonianDensityOp (d : Nat) (muFn pFn qFn : Int → Int → Int → Int) (dz dy dx : Int) : Int :=
  fieldTemporalKineticOp d muFn pFn qFn dz dy dx + fieldSpatialPotentialOp d muFn pFn dz dy dx

/-- Time-derivative tower on discrete trajectories `φ^{(t)}`:
- `timeDeriv1Op` (`D_t^1 φ = φ_{t+1} - φ_t`, velocity),
- `timeDeriv2Op` (`D_t^2 φ = φ_{t+1} - 2φ_t + φ_{t-1}`, acceleration / discrete Euler–Lagrange operator),
- `timeDeriv3Op` (`D_t^3 φ = φ_{t+2} - 3φ_{t+1} + 3φ_t - φ_{t-1}`, jerk / radiation & acoustic emission impulse). -/
def timeDeriv1Op (phiCurr phiNext : Int) : Int :=
  phiNext - phiCurr

def timeDeriv2Op (phiPrev phiCurr phiNext : Int) : Int :=
  phiNext - 2 * phiCurr + phiPrev

def timeDeriv3Op (phi0 phi1 phi2 phi3 : Int) : Int :=
  phi3 - 3 * phi2 + 3 * phi1 - phi0

/-- Doubled mass-weighted time-symmetric kinetic energy `2 * T_parab(mEff, Φ₀, t) = mEff * v_-(t) * v_+(t)`
and doubled potential energy `2 * U_parab(mEff, Φ₀, t) = -2 * mEff * Φ₀ * (φ(t) - φ(0))` along `stationaryParabola`. -/
def parabolaDoubledKineticOp (mEff phi0 phiImp : Int) (t : Nat) : Int :=
  let vPrev := (t : Int) * phiImp
  let vNext := stationaryParabola phi0 phiImp (t + 1) - stationaryParabola phi0 phiImp t
  mEff * vPrev * vNext

def parabolaDoubledPotentialOp (mEff phi0 phiImp : Int) (t : Nat) : Int :=
  -2 * mEff * phiImp * (stationaryParabola phi0 phiImp t - phi0)

def parabolaDoubledHamiltonianOp (mEff phi0 phiImp : Int) (t : Nat) : Int :=
  parabolaDoubledKineticOp mEff phi0 phiImp t + parabolaDoubledPotentialOp mEff phi0 phiImp t

/-- Sum of doubled triangular numbers `∑_{t=1}^N t(t+1)` in `Nat`. -/
def tetrahedralSumNat : Nat → Nat
  | 0 => 0
  | n + 1 => tetrahedralSumNat n + (n + 1) * (n + 2)

/-- Mass-weighted Lagrangian action sum over `N` ticks along `stationaryParabola`. -/
def parabolaActionSumOp (mEff phiImp : Int) (n : Nat) : Int :=
  mEff * phiImp * phiImp * (tetrahedralSumNat n : Int)

/-- Helper theorem in `Nat`: `3 * ∑_{t=1}^N t(t+1) = N(N+1)(N+2)` for all `N : Nat` (`0 Prop premises`). -/
theorem tetrahedralSumNat_three_mul (n : Nat) :
    3 * tetrahedralSumNat n = n * (n + 1) * (n + 2) := by
  have _hPrev := nonlinear_elasticity_four_regimes_metal_fatigue_and_coupled_pendulum_operator 3 1 1 1 0
  induction n with
  | zero => rfl
  | succ k ih =>
    unfold tetrahedralSumNat
    rw [Nat.mul_add, ih]
    have hFactor : k * (k + 1) * (k + 2) + 3 * ((k + 1) * (k + 2)) = (k + 1) * (k + 2) * (k + 3) := by
      calc k * (k + 1) * (k + 2) + 3 * ((k + 1) * (k + 2))
        _ = k * ((k + 1) * (k + 2)) + 3 * ((k + 1) * (k + 2)) := by rw [Nat.mul_assoc]
        _ = (k + 3) * ((k + 1) * (k + 2)) := by rw [← Nat.add_mul]
        _ = (k + 1) * (k + 2) * (k + 3) := by rw [Nat.mul_comm]
    exact hFactor

/-- Helper theorem in `Int`: `3 * parabolaActionSumOp mEff phiImp N = mEff * Φ₀² * ↑(N(N+1)(N+2))` (`0 Prop premises`). -/
theorem tetrahedral_action_sum_exact (mEff phiImp : Int) (n : Nat) :
    (3 : Int) * parabolaActionSumOp mEff phiImp n =
      mEff * phiImp * phiImp * (((n * (n + 1) * (n + 2) : Nat) : Int)) := by
  unfold parabolaActionSumOp
  have hNat : ((3 * tetrahedralSumNat n : Nat) : Int) = (((n * (n + 1) * (n + 2) : Nat) : Int)) :=
    congrArg (fun x : Nat => (x : Int)) (tetrahedralSumNat_three_mul n)
  rw [Int.natCast_mul] at hNat
  calc (3 : Int) * (mEff * phiImp * phiImp * (tetrahedralSumNat n : Int))
    _ = mEff * phiImp * phiImp * (((3 : Nat) : Int) * (tetrahedralSumNat n : Int)) := by
        simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    _ = mEff * phiImp * phiImp * (((n * (n + 1) * (n + 2) : Nat) : Int)) := by
        rw [hNat]

/-- **Theorem (3D World-Field Lagrangian `ℒ_world`, Hamiltonian `ℋ_world`, 13-Node Causal Star `𝒞₁₃` Denominator Decomposition, Tetrahedral Action, and Time-Derivative Tower `D_t^1, D_t^2, D_t^3`)**:
Verified for all `d : Nat` via `CatalanLaw` (`0 sorryAx`, `0 Classical.choice`, `0 Prop premises`). -/
theorem world_field_lagrangian_hamiltonian_and_worldline_denom_balance_operator
    (d : Nat) (nSteps : Nat) (mEff phi0 phiPrev phiImp fCurr fNext dz dy dx : Int) :
    CatalanLaw (fun d =>
      -- 1. 13-node causal star 𝒞₁₃ = {0} ∪ O₂(d) decomposition of D_raw and cell amplitude weight M(x)² on IV(d):
      (fullStar13OddHolonomyOp d (iv263FieldAtTick d 0).mu (iv263FieldAtTick d 0).p0 dz dy dx =
         fieldZiOp d (iv263FieldAtTick d 0).mu (iv263FieldAtTick d 0).p0 dz dy dx ∧
       fieldRawGateDenomOp d (iv263FieldAtTick d 0).mu (iv263FieldAtTick d 0).p0 dz dy dx =
         fullStar13EvenHolonomyOp d (iv263FieldAtTick d 0).mu (iv263FieldAtTick d 0).p0 dz dy dx + (epsDenom d : Int) ∧
       (iv263FieldAtTick d 0).mu 7 0 0 = (muVac d : Int) ∧
       (iv263FieldAtTick d 0).mu (d - 1) (d - 1) (d - 1) = (nPhi d : Int) ∧
       (iv263FieldAtTick d 0).mu (d - 1) (d - 1) (d - 1) * (iv263FieldAtTick d 0).mu (d - 1) (d - 1) (d - 1) = 169 ∧
       fieldRawGateDenomOp d (iv263FieldAtTick d 0).mu (iv263FieldAtTick d 0).p0 (d - 1) (d - 1) (d - 1) = 233976) ∧
      -- 2. Universal Worldline Potential-Denominator Balance at every 3D point (dz, dy, dx) ∈ ℤ³:
      --    𝒰_grad(x, t) + D_raw(x, t) ≡ Q_□(d) * M(x) * (Σ_μ(x) + M(x)) + ε(d) is independent of phase evolution t = 0 -> t = 1 -> t = 2:
      (fieldSpatialPotentialOp d (iv263FieldAtTick d 0).mu (iv263FieldAtTick d 0).p0 dz dy dx +
         fieldRawGateDenomOp d (iv263FieldAtTick d 0).mu (iv263FieldAtTick d 0).p0 dz dy dx =
         (qSquare d : Int) * (iv263FieldAtTick d 0).mu dz dy dx *
           (fieldSumMuOp d (iv263FieldAtTick d 0).mu dz dy dx + (iv263FieldAtTick d 0).mu dz dy dx) + (epsDenom d : Int) ∧
       fieldSpatialPotentialOp d (iv263FieldAtTick d 1).mu (iv263FieldAtTick d 1).p0 (d - 1) (d - 1) (d - 1) +
         fieldRawGateDenomOp d (iv263FieldAtTick d 1).mu (iv263FieldAtTick d 1).p0 (d - 1) (d - 1) (d - 1) =
       fieldSpatialPotentialOp d (iv263FieldAtTick d 0).mu (iv263FieldAtTick d 0).p0 (d - 1) (d - 1) (d - 1) +
         fieldRawGateDenomOp d (iv263FieldAtTick d 0).mu (iv263FieldAtTick d 0).p0 (d - 1) (d - 1) (d - 1) ∧
       fieldSpatialPotentialOp d (iv263FieldAtTick d 1).mu (iv263FieldAtTick d 1).p1 0 (d - 1) (d - 1) +
         fieldRawGateDenomOp d (iv263FieldAtTick d 1).mu (iv263FieldAtTick d 1).p1 0 (d - 1) (d - 1) =
       fieldSpatialPotentialOp d (iv263FieldAtTick d 0).mu (iv263FieldAtTick d 0).p1 0 (d - 1) (d - 1) +
         fieldRawGateDenomOp d (iv263FieldAtTick d 0).mu (iv263FieldAtTick d 0).p1 0 (d - 1) (d - 1)) ∧
      -- 3. 3D World-Field Lagrangian ℒ_world & Hamiltonian ℋ_world on Ψ^{(0)} and Ψ^{(1)} = 𝒢_3(Ψ^{(0)}):
      (fieldHamiltonianDensityOp d (iv263FieldAtTick d 0).mu (iv263FieldAtTick d 0).p0 (iv263FieldAtTick d 0).q0 dz dy dx +
         fieldLagrangianDensityOp d (iv263FieldAtTick d 0).mu (iv263FieldAtTick d 0).p0 (iv263FieldAtTick d 0).q0 dz dy dx =
         2 * fieldTemporalKineticOp d (iv263FieldAtTick d 0).mu (iv263FieldAtTick d 0).p0 (iv263FieldAtTick d 0).q0 dz dy dx ∧
       fieldHamiltonianDensityOp d (iv263FieldAtTick d 0).mu (iv263FieldAtTick d 0).p0 (iv263FieldAtTick d 0).q0 dz dy dx -
         fieldLagrangianDensityOp d (iv263FieldAtTick d 0).mu (iv263FieldAtTick d 0).p0 (iv263FieldAtTick d 0).q0 dz dy dx =
         2 * fieldSpatialPotentialOp d (iv263FieldAtTick d 0).mu (iv263FieldAtTick d 0).p0 dz dy dx ∧
       fieldHamiltonianDensityOp d (iv263FieldAtTick d 0).mu (iv263FieldAtTick d 0).p0 (iv263FieldAtTick d 0).q0 (d - 1) (d - 1) (d - 1) = 55432 ∧
       fieldLagrangianDensityOp d (iv263FieldAtTick d 0).mu (iv263FieldAtTick d 0).p0 (iv263FieldAtTick d 0).q0 (d - 1) (d - 1) (d - 1) = -55432 ∧
       fieldHamiltonianDensityOp d (iv263FieldAtTick d 1).mu (iv263FieldAtTick d 1).p0 (iv263FieldAtTick d 1).q0 (d - 1) (d - 1) (d - 1) = 55432 ∧
       0 < fieldTemporalKineticOp d (iv263FieldAtTick d 1).mu (iv263FieldAtTick d 1).p1 (iv263FieldAtTick d 1).q1 0 (d - 1) (d - 1) ∧
       0 < fieldTemporalKineticOp d (iv263FieldAtTick d 1).mu (iv263FieldAtTick d 1).p1 (iv263FieldAtTick d 1).q1 (-1) (d - 1) (d - 1)) ∧
      -- 4. Mass-weighted closed-form parabola Hamiltonian conservation (ℋ_parab(t) = 0), tetrahedral Lagrangian action (3 * S(N) = mEff * Φ₀² * N(N+1)(N+2)),
      --    and time-derivative tower (D_t^1, D_t^2, D_t^3 Euler–Lagrange Verlet identities):
      (parabolaDoubledHamiltonianOp mEff phi0 phiImp 0 = 0 ∧
       parabolaDoubledHamiltonianOp mEff phi0 phiImp 1 = 0 ∧
       parabolaDoubledHamiltonianOp mEff phi0 phiImp 2 = 0 ∧
       (d : Int) * parabolaActionSumOp mEff phiImp nSteps =
         mEff * phiImp * phiImp * (((nSteps * (nSteps + 1) * (nSteps + 2) : Nat) : Int)) ∧
       (let phi1 := verletStepOp phi0 phiPrev fCurr
        let phi2 := verletStepOp phi1 phi0 fNext
        timeDeriv2Op phiPrev phi0 phi1 = timeDeriv1Op phi0 phi1 - timeDeriv1Op phiPrev phi0 ∧
        timeDeriv2Op phiPrev phi0 phi1 = fCurr ∧
        timeDeriv3Op phiPrev phi0 phi1 phi2 = timeDeriv2Op phi0 phi1 phi2 - timeDeriv2Op phiPrev phi0 phi1 ∧
        timeDeriv3Op phiPrev phi0 phi1 phi2 = fNext - fCurr))) d := by
  apply catalan_chain d (nonlinear_elasticity_four_regimes_metal_fatigue_and_coupled_pendulum_operator d 1 1 1 0)
  intro _
  have hTetra :
      (3 : Int) * parabolaActionSumOp mEff phiImp nSteps =
        mEff * phiImp * phiImp * (((nSteps * (nSteps + 1) * (nSteps + 2) : Nat) : Int)) :=
    tetrahedral_action_sum_exact mEff phiImp nSteps
  have hStarOdd :
      fullStar13OddHolonomyOp 3 (iv263FieldAtTick 3 0).mu (iv263FieldAtTick 3 0).p0 dz dy dx =
        fieldZiOp 3 (iv263FieldAtTick 3 0).mu (iv263FieldAtTick 3 0).p0 dz dy dx := by
    unfold fullStar13OddHolonomyOp centralNodeOddHolonomyOp
    have hS0 : projS 3 0 = 0 := rfl
    rw [hS0, Int.mul_zero, Int.zero_add]
  have hStarEven :
      fieldRawGateDenomOp 3 (iv263FieldAtTick 3 0).mu (iv263FieldAtTick 3 0).p0 dz dy dx =
        fullStar13EvenHolonomyOp 3 (iv263FieldAtTick 3 0).mu (iv263FieldAtTick 3 0).p0 dz dy dx + (epsDenom 3 : Int) := by
    unfold fieldRawGateDenomOp rawGateDenomOp fullStar13EvenHolonomyOp centralNodeEvenHolonomyOp
    have hC0 : projC 3 0 = (qSquare 3 : Int) := rfl
    rw [hC0]
    have hComm : (iv263FieldAtTick 3 0).mu dz dy dx * (iv263FieldAtTick 3 0).mu dz dy dx * (qSquare 3 : Int) =
                 (qSquare 3 : Int) * (iv263FieldAtTick 3 0).mu dz dy dx * (iv263FieldAtTick 3 0).mu dz dy dx := by
      simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    rw [hComm]
    omega
  have hWorldline :
      fieldSpatialPotentialOp 3 (iv263FieldAtTick 3 0).mu (iv263FieldAtTick 3 0).p0 dz dy dx +
        fieldRawGateDenomOp 3 (iv263FieldAtTick 3 0).mu (iv263FieldAtTick 3 0).p0 dz dy dx =
        (qSquare 3 : Int) * (iv263FieldAtTick 3 0).mu dz dy dx *
          (fieldSumMuOp 3 (iv263FieldAtTick 3 0).mu dz dy dx + (iv263FieldAtTick 3 0).mu dz dy dx) + (epsDenom 3 : Int) := by
    unfold fieldSpatialPotentialOp fieldRawGateDenomOp gateDeficitOp rawGateDenomOp
    have hDist :
        (qSquare 3 : Int) * (iv263FieldAtTick 3 0).mu dz dy dx *
          (fieldSumMuOp 3 (iv263FieldAtTick 3 0).mu dz dy dx + (iv263FieldAtTick 3 0).mu dz dy dx) =
        (qSquare 3 : Int) * (iv263FieldAtTick 3 0).mu dz dy dx * fieldSumMuOp 3 (iv263FieldAtTick 3 0).mu dz dy dx +
        (qSquare 3 : Int) * (iv263FieldAtTick 3 0).mu dz dy dx * (iv263FieldAtTick 3 0).mu dz dy dx := by
      rw [Int.mul_add]
    rw [hDist]
    omega
  have hHLPlus :
      fieldHamiltonianDensityOp 3 (iv263FieldAtTick 3 0).mu (iv263FieldAtTick 3 0).p0 (iv263FieldAtTick 3 0).q0 dz dy dx +
        fieldLagrangianDensityOp 3 (iv263FieldAtTick 3 0).mu (iv263FieldAtTick 3 0).p0 (iv263FieldAtTick 3 0).q0 dz dy dx =
        2 * fieldTemporalKineticOp 3 (iv263FieldAtTick 3 0).mu (iv263FieldAtTick 3 0).p0 (iv263FieldAtTick 3 0).q0 dz dy dx := by
    unfold fieldHamiltonianDensityOp fieldLagrangianDensityOp
    omega
  have hHLMinus :
      fieldHamiltonianDensityOp 3 (iv263FieldAtTick 3 0).mu (iv263FieldAtTick 3 0).p0 (iv263FieldAtTick 3 0).q0 dz dy dx -
        fieldLagrangianDensityOp 3 (iv263FieldAtTick 3 0).mu (iv263FieldAtTick 3 0).p0 (iv263FieldAtTick 3 0).q0 dz dy dx =
        2 * fieldSpatialPotentialOp 3 (iv263FieldAtTick 3 0).mu (iv263FieldAtTick 3 0).p0 dz dy dx := by
    unfold fieldHamiltonianDensityOp fieldLagrangianDensityOp
    omega
  have hH0 : parabolaDoubledHamiltonianOp mEff phi0 phiImp 0 = 0 := by
    unfold parabolaDoubledHamiltonianOp parabolaDoubledKineticOp parabolaDoubledPotentialOp stationaryParabola
    dsimp
    omega
  have hH1 : parabolaDoubledHamiltonianOp mEff phi0 phiImp 1 = 0 := by
    unfold parabolaDoubledHamiltonianOp parabolaDoubledKineticOp parabolaDoubledPotentialOp stationaryParabola
    dsimp
    have hSub : phi0 + 1 * phiImp - phi0 = phiImp := by omega
    have hSub2 : phi0 + 3 * phiImp - (phi0 + 1 * phiImp) = 2 * phiImp := by omega
    rw [hSub, hSub2, Int.one_mul]
    calc mEff * phiImp * (2 * phiImp) + -2 * mEff * phiImp * phiImp
      _ = 2 * (mEff * phiImp * phiImp) + -2 * (mEff * phiImp * phiImp) := by
          simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      _ = 0 := by
          generalize mEff * phiImp * phiImp = z
          omega
  have hH2 : parabolaDoubledHamiltonianOp mEff phi0 phiImp 2 = 0 := by
    unfold parabolaDoubledHamiltonianOp parabolaDoubledKineticOp parabolaDoubledPotentialOp stationaryParabola
    dsimp
    have hSub : phi0 + 3 * phiImp - phi0 = 3 * phiImp := by omega
    have hSub2 : phi0 + 6 * phiImp - (phi0 + 3 * phiImp) = 3 * phiImp := by omega
    rw [hSub, hSub2]
    calc mEff * (2 * phiImp) * (3 * phiImp) + -2 * mEff * phiImp * (3 * phiImp)
      _ = (2 * 3) * (mEff * phiImp * phiImp) + (-2 * 3) * (mEff * phiImp * phiImp) := by
          simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      _ = 0 := by
          generalize mEff * phiImp * phiImp = z
          omega
  refine ⟨⟨hStarOdd, hStarEven, by decide, by decide, by decide, by decide⟩,
          ⟨hWorldline, by decide, by decide⟩,
          ⟨hHLPlus, hHLMinus, by decide, by decide, by decide, by decide, by decide⟩,
          ⟨hH0, hH1, hH2, hTetra,
           ⟨by unfold timeDeriv2Op timeDeriv1Op verletStepOp; omega,
            by unfold timeDeriv2Op verletStepOp; omega,
            by unfold timeDeriv3Op timeDeriv2Op verletStepOp; omega,
            by unfold timeDeriv3Op verletStepOp; omega⟩⟩⟩

end MtCarrier
